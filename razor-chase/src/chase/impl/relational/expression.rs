use crate::chase::E;
use anyhow::{bail, Result};
use razor_fol::syntax::{Formula, Pred, V};
use relalg::{expression::Mono, *};
use std::ops::Deref;

pub(crate) type Tup = Vec<E>;

trait TupleMap: FnMut(&Tup) -> Tup {}
impl<F: FnMut(&Tup) -> Tup> TupleMap for F {}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Attributes(pub(crate) Vec<V>);

impl Attributes {
    pub(crate) fn union(&self, other: &Attributes) -> Attributes {
        let mut result = self.iter().map(|v| v.clone()).collect::<Vec<V>>();
        let diff = other
            .iter()
            .filter(|v| !self.contains(v))
            .map(|v| v.clone())
            .collect::<Vec<V>>();
        result.extend(diff);
        Self(result)
    }

    pub(crate) fn intersect(&self, other: &Attributes) -> Attributes {
        Self(
            self.iter()
                .filter(|v| other.contains(v))
                .map(|v| (*v).clone())
                .collect(),
        )
    }

    pub(crate) fn retain(&mut self, other: &Self) {
        self.0.retain(|x| other.contains(x));
    }
}

impl Deref for Attributes {
    type Target = Vec<V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Vec<V>> for Attributes {
    fn from(vars: Vec<V>) -> Self {
        Self(vars)
    }
}

pub(crate) struct SubExp {
    attributes: Attributes,
    join_key: Box<dyn TupleMap>,
    pub(crate) expression: Mono<Tup>,
}

fn make_key(key_attrs: &Attributes, attrs: &Attributes) -> impl TupleMap {
    let mut key_indices = Vec::new();
    for v in &key_attrs.0 {
        let mut iter = attrs.iter();
        key_indices.push(iter.position(|item| item == v).unwrap().clone());
    }

    move |t: &Tup| {
        let mut key = vec![];
        key_indices.iter().for_each(|i| {
            key.push(t[*i]);
        });
        key
    }
}

fn make_relation(
    pred: &Pred,
    vars: &Vec<&V>,
    key_attrs: &Attributes,
    attrs: &Attributes,
) -> Result<SubExp> {
    let mut project_attrs = Vec::new();
    let mut project_indices = Vec::new();
    for v in &attrs.0 {
        let mut vars_iter = vars.iter();
        if let Some(p) = vars_iter.position(|item| *item == v) {
            project_indices.push(p);
            project_attrs.push(v.clone());
        }
    }

    // TODO: probably don't need to project keys yet
    let project = Project::new(
        &Box::new(Mono::Relation(Relation::<Tup>::new(&pred.0))),
        move |p| {
            let mut project = vec![];
            project_indices.iter().for_each(|i| {
                project.push(p[*i]);
            });
            project
        },
    );

    let project_attrs: Attributes = project_attrs.into();
    let join_key = make_key(&key_attrs, &project_attrs);

    Ok(SubExp {
        attributes: project_attrs,
        join_key: Box::new(join_key),
        expression: Mono::Project(project),
    })
}

fn make_join(
    left: &Formula,
    right: &Formula,
    key_attrs: &Attributes,
    attrs: &Attributes,
) -> Result<SubExp> {
    enum JoinTuple {
        Left(usize),
        Right(usize),
    }

    let left_attrs = Attributes::from(
        left.free_vars()
            .iter()
            .map(|v| (*v).clone())
            .collect::<Vec<V>>(),
    );
    let right_attrs = Attributes::from(
        right
            .free_vars()
            .iter()
            .map(|v| (*v).clone())
            .collect::<Vec<V>>(),
    );
    let common_vars = left_attrs.intersect(&right_attrs);

    let left_exp = make_expression(left, &common_vars, &attrs.union(&right_attrs))?;
    let right_exp = make_expression(right, &common_vars, &attrs.union(&left_exp.attributes))?;

    let mut join_indices = Vec::new();
    let mut join_attrs = Vec::new();
    for v in &attrs.0 {
        let mut left_iter = left_exp.attributes.0.iter();
        let mut right_iter = right_exp.attributes.0.iter();

        if let Some(p) = left_iter.position(|item| item == v) {
            join_indices.push(JoinTuple::Left(p));
            join_attrs.push(v.clone());
        } else if let Some(p) = right_iter.position(|item| item == v) {
            join_indices.push(JoinTuple::Right(p));
            join_attrs.push(v.clone());
        }
    }

    let join_attrs: Attributes = join_attrs.into();
    let join_key = make_key(&key_attrs, &join_attrs);

    let join = Join::new(
        &Box::new(left_exp.expression),
        &Box::new(right_exp.expression),
        left_exp.join_key,
        right_exp.join_key,
        move |_, l, r| {
            let mut project = vec![];
            join_indices.iter().for_each(|i| match i {
                JoinTuple::Left(i) => project.push(l[*i]),
                JoinTuple::Right(i) => project.push(r[*i]),
            });
            project
        },
    );

    Ok(SubExp {
        attributes: join_attrs,
        join_key: Box::new(join_key),
        expression: Mono::Join(join),
    })
}

fn make_union(
    left: &Formula,
    right: &Formula,
    join_attrs: &Attributes,
    attrs: &Attributes,
) -> Result<SubExp> {
    let left_exp = make_expression(left, join_attrs, attrs)?;
    let right_exp = make_expression(right, join_attrs, attrs)?;

    assert_eq!(left_exp.attributes, right_exp.attributes);

    let union = Union::new(
        &Box::new(left_exp.expression),
        &Box::new(right_exp.expression),
    );
    Ok(SubExp {
        attributes: left_exp.attributes,
        join_key: left_exp.join_key, // irrelevant
        expression: Mono::Union(union),
    })
}

#[allow(unused)]
// Assumes the input is a range restricted relationalized formula.
// FIXME: fix the recursion so it doesn't allow unexpected formula structure.
pub(crate) fn make_expression(
    formula: &Formula,
    join_attr: &Attributes,
    final_attr: &Attributes,
) -> Result<SubExp> {
    match formula {
        Formula::Bottom => Ok(SubExp {
            attributes: Vec::new().into(),
            join_key: Box::new(|t| t.clone()),
            expression: Mono::Empty(Empty::new()),
        }),
        Formula::Top => Ok(SubExp {
            attributes: Vec::new().into(),
            join_key: Box::new(|t| t.clone()),
            expression: Mono::Singleton(Singleton(vec![].into())),
        }),
        Formula::Atom {
            predicate,
            terms: _,
        } => make_relation(predicate, &formula.free_vars(), &join_attr, &final_attr),
        Formula::And { left, right } => make_join(left, right, join_attr, final_attr),
        Formula::Or { left, right } => make_union(left, right, join_attr, final_attr),
        // Formula::Or { left, right } => todo!(),
        _ => bail!("expecting a relational formula"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use razor_fol::{formula, v};
    use relalg::{relalg, Database, Tuples};

    fn setup_database() -> Result<Database> {
        let mut db = Database::new();
        let p = relalg! { create relation "P":[Tup] in db }?;
        let q = relalg! { create relation "Q":[Tup] in db }?;
        let r = relalg! { create relation "R":[Tup] in db }?;

        relalg! (insert into (p) values [vec![E(1)], vec![E(2)], vec![E(3)]] in db)?;
        relalg! (insert into (q) values [vec![E(20), E(200)], vec![E(30), E(300)], vec![E(40), E(400)]] in db)?;
        relalg! (insert into (r) values [vec![E(2), E(20)], vec![E(3), E(30)], vec![E(4), E(40)]] in db)?;

        Ok(db)
    }

    #[test]
    fn test_atom() -> Result<()> {
        let db = setup_database()?;
        {
            let formula = formula!(P(x));
            let result = make_expression(&formula, &vec![].into(), &vec![v!(x)].into())?;
            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!(P(x));
            let result = make_expression(&formula, &vec![v!(x)].into(), &vec![v!(x)].into())?;
            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!(Q(x, y));
            let result = make_expression(&formula, &vec![].into(), &vec![v!(x), v!(y)].into())?;
            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(20), E(200)],
                    vec![E(30), E(300)],
                    vec![E(40), E(400)],
                ]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = formula!(Q(x, y));
            let result = make_expression(
                &formula,
                &vec![v!(x), v!(y)].into(),
                &vec![v!(y), v!(x)].into(),
            )?;
            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(200), E(20)],
                    vec![E(300), E(30)],
                    vec![E(400), E(40)],
                ]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(y), v!(x)]), result.attributes);
        }
        {
            let formula = formula!(Q(x, y));
            let result =
                make_expression(&formula, &vec![v!(x)].into(), &vec![v!(x), v!(x)].into())?;
            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(20), E(20)],
                    vec![E(30), E(30)],
                    vec![E(40), E(40)],
                ]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x), v!(x)]), result.attributes);
        }

        // TODO maybe support Q(x, x)?
        Ok(())
    }

    #[test]
    fn test_and() -> Result<()> {
        let db = setup_database()?;
        {
            let formula = formula!([P(x)] & [R(y, z)]);
            let result =
                make_expression(&formula, &vec![].into(), &vec![v!(x), v!(y), v!(z)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(1), E(2), E(20)],
                    vec![E(1), E(3), E(30)],
                    vec![E(1), E(4), E(40)],
                    vec![E(2), E(2), E(20)],
                    vec![E(2), E(3), E(30)],
                    vec![E(2), E(4), E(40)],
                    vec![E(3), E(2), E(20)],
                    vec![E(3), E(3), E(30)],
                    vec![E(3), E(4), E(40)],
                ]),
                tuples
            );
            assert_eq!(
                Attributes::from(vec![v!(x), v!(y), v!(z)]),
                result.attributes
            );
        }
        {
            let formula = formula!([P(x)] & [R(y, x)]);
            let result = make_expression(&formula, &vec![].into(), &vec![v!(x), v!(y)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(Tuples { items: vec![] }, tuples);
            assert_eq!(Attributes::from(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [R(x, y)]);
            let result =
                make_expression(&formula, &vec![v!(y)].into(), &vec![v!(x), v!(y)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(2), E(20)], vec![E(3), E(30)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [Q(y, z)]);
            let result = make_expression(
                &formula,
                &vec![v!(x), v!(y)].into(),
                &vec![v!(y), v!(x)].into(),
            )?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(20), E(1)],
                    vec![E(30), E(1)],
                    vec![E(40), E(1)],
                    vec![E(20), E(2)],
                    vec![E(30), E(2)],
                    vec![E(40), E(2)],
                    vec![E(20), E(3)],
                    vec![E(30), E(3)],
                    vec![E(40), E(3)],
                ]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(y), v!(x)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [Q(y, z)]);
            let result = make_expression(
                &formula,
                &vec![v!(y), v!(x)].into(),
                &vec![v!(x), v!(y)].into(),
            )?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(1), E(20)],
                    vec![E(2), E(20)],
                    vec![E(3), E(20)],
                    vec![E(1), E(30)],
                    vec![E(2), E(30)],
                    vec![E(3), E(30)],
                    vec![E(1), E(40)],
                    vec![E(2), E(40)],
                    vec![E(3), E(40)],
                ]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x), v!(y)]), result.attributes);
        }

        Ok(())
    }

    #[test]
    fn test_union() -> Result<()> {
        let db = setup_database()?;
        {
            let formula = formula!([Q(x, y)] | [R(y, x)]);
            let result = make_expression(&formula, &vec![].into(), &vec![v!(x), v!(y)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(20), E(2)],
                    vec![E(30), E(3)],
                    vec![E(40), E(4)],
                    vec![E(20), E(200)],
                    vec![E(30), E(300)],
                    vec![E(40), E(400)],
                ]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x), v!(y)]), result.attributes);
        }

        {
            let formula = formula!([Q(x, y)] | [R(y, x)]);
            let result = make_expression(&formula, &vec![].into(), &vec![v!(y)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(2)],
                    vec![E(3)],
                    vec![E(4)],
                    vec![E(200)],
                    vec![E(300)],
                    vec![E(400)],
                ]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(y)]), result.attributes);
        }

        Ok(())
    }

    #[test]
    fn test_formula() -> Result<()> {
        let db = setup_database()?;
        {
            let formula = formula!({ [P(x)] & [P(x)] } & { P(x) });
            let result = make_expression(&formula, &vec![v!(x)].into(), &vec![v!(x)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y)] });
            let result = make_expression(&formula, &vec![v!(x)].into(), &vec![v!(x)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y, z)] });
            let result = make_expression(
                &formula,
                &vec![v!(z)].into(),
                &vec![v!(y), v!(x), v!(z)].into(),
            )?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![
                    vec![E(20), E(1), E(200)],
                    vec![E(20), E(2), E(200)],
                    vec![E(20), E(3), E(200)],
                    vec![E(30), E(1), E(300)],
                    vec![E(30), E(2), E(300)],
                    vec![E(30), E(3), E(300)],
                    vec![E(40), E(1), E(400)],
                    vec![E(40), E(2), E(400)],
                    vec![E(40), E(3), E(400)],
                ]),
                tuples
            );
            assert_eq!(
                Attributes::from(vec![v!(y), v!(x), v!(z)]),
                result.attributes
            );
        }
        Ok(())
    }
}
