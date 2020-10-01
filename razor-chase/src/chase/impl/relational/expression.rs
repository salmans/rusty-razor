/*! Implements the algorithm for converting a relational formula to a relational expression in `relalg`.*/

use crate::chase::E;
use anyhow::{bail, Result};
use razor_fol::syntax::{Formula, Pred};
use relalg::{expression::Mono, *};
use std::ops::Deref;

/// Is the type of tuples in database instances.
pub(super) type Tuple = Vec<E>;

/// Is the trait of objects that map a tuple to another.
trait TupleMap: FnMut(&Tuple) -> Tuple {}
impl<F: FnMut(&Tuple) -> Tuple> TupleMap for F {}

/// In the context of a relational expression, a variable is refered to as an `Attribute`.
/// In fact, every position on a relational formula is an attribute.
/// However, because every position is occupied by a unique variable, every
/// variable identifies an attribute.
type Attribute = razor_fol::syntax::V;

/// Represents the attributes of a relational expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Attributes(Vec<Attribute>);

impl Attributes {
    /// Returns the set union of the attributes in the receiver and those in `other`.
    pub fn union(&self, other: &Attributes) -> Attributes {
        self.iter()
            .chain(other.iter().filter(|v| !self.contains(v)))
            .cloned()
            .collect::<Vec<_>>()
            .into()
    }

    /// Returns the attributes that are present in both the receiver and `other`.
    pub fn intersect(&self, other: &Attributes) -> Attributes {
        self.iter()
            .filter(|v| other.contains(v))
            .cloned()
            .collect::<Vec<_>>()
            .into()
    }

    /// Makes a `TupleMap` closure that given a `Tuple` over the attributes of the receiver,
    /// returns a `Tuple` projected by `attributes`.
    fn project(&self, attributes: &Attributes) -> impl TupleMap {
        let mut key_indices = Vec::new();
        for v in &attributes.0 {
            let mut iter = self.iter();
            key_indices.push(iter.position(|item| item == v).unwrap().clone());
        }

        move |t: &Tuple| {
            let mut key = vec![];
            key_indices.iter().for_each(|i| {
                key.push(t[*i]);
            });
            key
        }
    }
}

impl Deref for Attributes {
    type Target = Vec<Attribute>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<I: IntoIterator<Item = Attribute>> From<I> for Attributes {
    fn from(attributes: I) -> Self {
        Self(attributes.into_iter().collect())
    }
}

/// Represents a relational expression of type `Mono<Tuple>` while the expression
/// is being constructed.
pub(super) struct SubExpression {
    /// Is the attributes associated to this expression.
    attributes: Attributes,

    /// Maps a tuple of `expression` to the keys that are used to join this subexpression with
    /// another subexpression at the upper level of the expression tree.
    join_key: Box<dyn TupleMap>,

    /// Is the (sub)expression in the context of a larger expression.
    expression: Mono<Tuple>,
}

impl SubExpression {
    /// Consumes the receiver and returns its `expression`.
    pub fn into_expression(self) -> Mono<Tuple> {
        self.expression
    }
}

/// Creates a relational expression (projection over an instance) for a predicate `pred` applied
/// to a list of variables `vars`. `key_attrs` is the expected key attributes for joining the
/// resulting subexpression with the subexpression at the upper level in the expression tree.
/// `attrs` is the expected attributes of the resulting subexpression.
fn atomic_expression(
    pred: &Pred,
    vars: &Vec<razor_fol::syntax::V>,
    key_attrs: &Attributes,
    attrs: &Attributes,
) -> Result<SubExpression> {
    let mut expr_attrs = Vec::new(); // attributes of the resulting expression
    let mut expr_indices = Vec::new(); // positions of those attributes in the tuple

    for v in attrs.iter() {
        let mut vars_iter = vars.iter();
        if let Some(p) = vars_iter.position(|item| item == v) {
            expr_indices.push(p);
            expr_attrs.push(v.clone());
        }
    }

    // The database instance containing tuples of `pred` is identified by `pred.to_string()`:
    let instance = Mono::Relation(Relation::<Tuple>::new(&pred.to_string()));

    // Project only the expected attributes of the instance:
    let project = Project::new(&Box::new(instance), move |p| {
        let mut projected_tuple = vec![];
        expr_indices.iter().for_each(|i| {
            projected_tuple.push(p[*i]);
        });
        projected_tuple
    });

    let expr_attrs: Attributes = expr_attrs.into();

    // `join_key` transforms a tuple to its expected keys:
    let join_key = expr_attrs.project(&key_attrs);

    Ok(SubExpression {
        attributes: expr_attrs,
        join_key: Box::new(join_key),
        expression: Mono::Project(project),
    })
}

/// Creates a join expression for the conjunction of `left` and `right`.
/// `key_attrs` is the expected key attributes for joining the
/// resulting subexpression with the subexpression at the upper level in the expression tree.
/// `attrs` is the expected attributes of the resulting subexpression.
fn and_expression(
    left: &Formula,
    right: &Formula,
    key_attrs: &Attributes,
    attrs: &Attributes,
) -> Result<SubExpression> {
    use either::Either;

    let left_attrs: Attributes = left
        .free_vars()
        .into_iter()
        .cloned()
        .collect::<Vec<_>>()
        .into();

    let right_attrs: Attributes = right
        .free_vars()
        .into_iter()
        .cloned()
        .collect::<Vec<_>>()
        .into();

    let common_vars = left_attrs.intersect(&right_attrs); // join key attributes of left and right

    let left_exp = expression(left, &common_vars, &attrs.union(&right_attrs))?;
    let right_exp = expression(right, &common_vars, &attrs.union(&left_exp.attributes))?;

    let mut expr_attrs = Vec::new(); // attributes of the resulting expression
    let mut expr_indices = Vec::new(); // indices of those attributes

    for v in attrs.iter() {
        let mut left_iter = left_exp.attributes.iter();
        let mut right_iter = right_exp.attributes.iter();

        // Is an expected attribute in the left or the right expression?
        if let Some(p) = left_iter.position(|item| item == v) {
            expr_indices.push(Either::Left(p));
            expr_attrs.push(v.clone());
        } else if let Some(p) = right_iter.position(|item| item == v) {
            expr_indices.push(Either::Right(p));
            expr_attrs.push(v.clone());
        }
    }

    let expr_attrs: Attributes = expr_attrs.into();
    let join_key = expr_attrs.project(&key_attrs); // join key for the expression on top

    let join = Join::new(
        &Box::new(left_exp.expression),
        &Box::new(right_exp.expression),
        left_exp.join_key,
        right_exp.join_key,
        move |_, l, r| {
            let mut projected_tuple = Vec::new();
            expr_indices.iter().for_each(|i| match i {
                Either::Left(i) => projected_tuple.push(l[*i]),
                Either::Right(i) => projected_tuple.push(r[*i]),
            });
            projected_tuple
        },
    );

    Ok(SubExpression {
        attributes: expr_attrs,
        join_key: Box::new(join_key),
        expression: Mono::Join(join),
    })
}

/// Creates a union expression for the disjunction of `left` and `right`.
/// `key_attrs` is the expected key attributes for joining the
/// resulting subexpression with the subexpression at the upper level in the expression tree.
/// `attrs` is the expected attributes of the resulting subexpression.
fn or_expression(
    left: &Formula,
    right: &Formula,
    key_attrs: &Attributes,
    attrs: &Attributes,
) -> Result<SubExpression> {
    // Disjuctions simply hope that left and right have the same attributes:
    let left_exp = expression(left, key_attrs, attrs)?;
    let right_exp = expression(right, key_attrs, attrs)?;

    assert_eq!(left_exp.attributes, right_exp.attributes);

    let union = Union::new(
        &Box::new(left_exp.expression),
        &Box::new(right_exp.expression),
    );
    Ok(SubExpression {
        attributes: left_exp.attributes,
        join_key: left_exp.join_key, // irrelevant
        expression: Mono::Union(union),
    })
}

/// Helper for `make_expression`.
fn expression(
    formula: &Formula,
    join_attr: &Attributes,
    final_attr: &Attributes,
) -> Result<SubExpression> {
    match formula {
        Formula::Bottom => Ok(SubExpression {
            attributes: Vec::new().into(),
            join_key: Box::new(|t| t.clone()),
            expression: Mono::Empty(Empty::new()),
        }),
        Formula::Top => Ok(SubExpression {
            attributes: Vec::new().into(),
            join_key: Box::new(|t| t.clone()),
            expression: Mono::Singleton(Singleton(vec![].into())),
        }),
        Formula::Atom {
            predicate,
            terms: _,
        } => {
            let free_vars = formula.free_vars().into_iter().cloned().collect();
            atomic_expression(predicate, &free_vars, &join_attr, &final_attr)
        }
        Formula::And { left, right } => and_expression(left, right, join_attr, final_attr),
        Formula::Or { left, right } => or_expression(left, right, join_attr, final_attr),
        _ => bail!("expecting a relational formula"),
    }
}

/// Given a relationalized formula, returns a relational expression.
pub(super) fn make_expression(formula: &Formula, attributes: &Attributes) -> Result<Mono<Tuple>> {
    expression(formula, &vec![].into(), attributes).map(SubExpression::into_expression)
}

#[cfg(test)]
mod tests {
    use super::*;
    use razor_fol::{formula, v};
    use relalg::{relalg, Database, Tuples};

    fn setup_database() -> Result<Database> {
        let mut db = Database::new();
        let p = relalg! { create relation "P":[Tuple] in db }?;
        let q = relalg! { create relation "Q":[Tuple] in db }?;
        let r = relalg! { create relation "R":[Tuple] in db }?;

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
            let result = expression(&formula, &vec![].into(), &vec![v!(x)].into())?;
            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!(P(x));
            let result = expression(&formula, &vec![v!(x)].into(), &vec![v!(x)].into())?;
            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!(Q(x, y));
            let result = expression(&formula, &vec![].into(), &vec![v!(x), v!(y)].into())?;
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
            let result = expression(
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
            let result = expression(&formula, &vec![v!(x)].into(), &vec![v!(x), v!(x)].into())?;
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
            let result = expression(&formula, &vec![].into(), &vec![v!(x), v!(y), v!(z)].into())?;

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
            let result = expression(&formula, &vec![].into(), &vec![v!(x), v!(y)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(Tuples { items: vec![] }, tuples);
            assert_eq!(Attributes::from(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [R(x, y)]);
            let result = expression(&formula, &vec![v!(y)].into(), &vec![v!(x), v!(y)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(2), E(20)], vec![E(3), E(30)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [Q(y, z)]);
            let result = expression(
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
            let result = expression(
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
            let result = expression(&formula, &vec![].into(), &vec![v!(x), v!(y)].into())?;

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
            let result = expression(&formula, &vec![].into(), &vec![v!(y)].into())?;

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
            let result = expression(&formula, &vec![v!(x)].into(), &vec![v!(x)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y)] });
            let result = expression(&formula, &vec![v!(x)].into(), &vec![v!(x)].into())?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(Attributes::from(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y, z)] });
            let result = expression(
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
