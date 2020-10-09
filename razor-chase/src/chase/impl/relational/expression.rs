/*! Implements the algorithm for converting a relational formula to a relational expression in `relalg`.*/

use super::{
    attribute::{Attribute, AttributeList},
    Tuple,
};
use anyhow::{bail, Result};
use either::Either;
use razor_fol::syntax::{Formula, Pred};
use relalg::{expression::Mono, *};

/// Represents the recursive structure of a relation expression as it is constructed.
#[derive(PartialEq, Eq, Hash, Debug)]
pub(super) enum RawExpression {
    Full,
    Empty,
    Relation(String),
    Project {
        expression: Box<RawExpression>,
        indices: Vec<u8>,
    },
    Join {
        left: Box<RawExpression>,
        right: Box<RawExpression>,
        indices: Vec<Either<u8, u8>>,
    },
    Union {
        left: Box<RawExpression>,
        right: Box<RawExpression>,
    },
}

impl RawExpression {
    fn boxed(self) -> Box<Self> {
        Box::new(self)
    }
}

/// Is the trait of objects that map a tuple to another.
pub(super) trait TupleMap: FnMut(&Tuple) -> Tuple + 'static {}
impl<F: FnMut(&Tuple) -> Tuple + 'static> TupleMap for F {}

impl AttributeList {
    /// Makes a `TupleMap` closure that given a `Tuple` over the attributes of the receiver,
    /// returns a `Tuple` projected by `attributes`.
    fn project(&self, attributes: &AttributeList) -> impl TupleMap {
        let mut key_indices = Vec::new();
        for v in attributes.attributes() {
            let mut iter = self.iter();
            key_indices.push(iter.position(|item| item == v).unwrap().clone());
        }

        let f = move |t: &Tuple| {
            let mut key = vec![];
            key_indices.iter().for_each(|i| {
                key.push(t[*i]);
            });
            key
        };
        f
    }
}

/// Represents a relational expression of type `Mono<Tuple>` while the expression
/// is being constructed.
pub(super) struct SubExpression {
    /// Is the attributes associated to this expression.
    attributes: AttributeList,

    /// Maps a tuple of `expression` to the keys that are used to join this subexpression with
    /// another subexpression at the upper level of the expression tree.
    join_key: Box<dyn TupleMap>,

    /// Is the (sub)expression in the context of a larger expression.
    expression: Mono<Tuple>,

    raw: RawExpression,
}

impl SubExpression {
    pub fn new(
        attributes: AttributeList,
        join_key: impl TupleMap,
        expression: Mono<Tuple>,
        raw: RawExpression,
    ) -> Self {
        Self {
            attributes,
            join_key: Box::new(join_key),
            expression,
            raw,
        }
    }

    /// Consumes the receiver and returns its `expression`.
    pub fn expression(&self) -> &Mono<Tuple> {
        &self.expression
    }

    pub fn set_expression(&mut self, expression: Mono<Tuple>) {
        self.expression = expression;
    }

    pub fn raw(&self) -> &RawExpression {
        &self.raw
    }

    /// Consumes the receiver and returns its `expression`.
    pub fn into_expression(self) -> Mono<Tuple> {
        self.expression
    }
}

/// Creates a relational expression (projection over an instance) for a predicate `pred` applied
/// to a list of variables `vars`. `key_attrs` is the expected key attributes for joining the
/// resulting subexpression with the subexpression at the upper level in the expression tree.
/// `attrs` is the expected attributes of the resulting subexpression.
pub(super) fn atomic_expression(
    pred: &Pred,
    vars: &Vec<razor_fol::syntax::V>,
    key_attrs: &AttributeList,
    attrs: &AttributeList,
) -> Result<SubExpression> {
    use std::convert::TryFrom;

    let vars = vars
        .into_iter()
        .map(Attribute::try_from)
        .collect::<Result<Vec<_>>>()?;
    let mut expr_attrs = Vec::new(); // attributes of the resulting expression
    let mut expr_indices = Vec::new(); // positions of those attributes in the tuple

    for attr in attrs.iter() {
        let mut vars_iter = vars.iter();
        if let Some(p) = vars_iter.position(|item| item == attr) {
            expr_indices.push(p);
            expr_attrs.push(attr.clone());
        }
    }

    let is_projected =
        attrs.len() != vars.len() || expr_indices.iter().zip(0..vars.len()).any(|(x, y)| *x != y);

    // The database instance containing tuples of `pred` is identified by `pred.to_string()`:
    let instance = Mono::Relation(Relation::<Tuple>::new(&pred.to_string()));
    let expr_attrs: AttributeList = expr_attrs.into();

    // `join_key` transforms a tuple to its expected keys:
    let key = expr_attrs.project(&key_attrs);

    let raw = if is_projected {
        RawExpression::Project {
            expression: RawExpression::Relation(pred.to_string()).boxed(),
            indices: expr_indices.iter().map(|&i| i as u8).collect(),
        }
    } else {
        RawExpression::Relation(pred.to_string())
    };

    // optimize identity projection:
    let expr = if is_projected {
        // Project only the expected attributes of the instance:
        let project = Project::new(&Box::new(instance), move |p| {
            let mut projected_tuple = vec![];
            expr_indices.iter().for_each(|i| {
                projected_tuple.push(p[*i]);
            });
            projected_tuple
        });
        Mono::Project(project)
    } else {
        instance
    };

    Ok(SubExpression::new(expr_attrs, key, expr, raw))
}

/// Creates a join expression for the conjunction of `left` and `right`.
/// `key_attrs` is the expected key attributes for joining the
/// resulting subexpression with the subexpression at the upper level in the expression tree.
/// `attrs` is the expected attributes of the resulting subexpression.
pub(super) fn and_expression(
    left: &Formula,
    right: &Formula,
    key_attrs: &AttributeList,
    attrs: &AttributeList,
) -> Result<SubExpression> {
    use std::convert::TryFrom;

    let left_attrs: AttributeList = left
        .free_vars()
        .into_iter()
        .map(Attribute::try_from)
        .collect::<Result<Vec<_>>>()?
        .into();
    let right_attrs: AttributeList = right
        .free_vars()
        .into_iter()
        .map(Attribute::try_from)
        .collect::<Result<Vec<_>>>()?
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

    let expr_attrs: AttributeList = expr_attrs.into();
    let join_key = expr_attrs.project(&key_attrs); // join key for the expression on top
    let raw = RawExpression::Join {
        left: left_exp.raw.boxed(),
        right: right_exp.raw.boxed(),
        indices: expr_indices.iter().map(|ei| ei.map(|i| i as u8)).collect(),
    };

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

    Ok(SubExpression::new(
        expr_attrs,
        join_key,
        Mono::Join(join),
        raw,
    ))
}

/// Creates a union expression for the disjunction of `left` and `right`.
/// `key_attrs` is the expected key attributes for joining the
/// resulting subexpression with the subexpression at the upper level in the expression tree.
/// `attrs` is the expected attributes of the resulting subexpression.
pub(super) fn or_expression(
    left: &Formula,
    right: &Formula,
    key_attrs: &AttributeList,
    attrs: &AttributeList,
) -> Result<SubExpression> {
    // Disjuctions simply hope that left and right have the same attributes:
    let left_exp = expression(left, key_attrs, attrs)?;
    let right_exp = expression(right, key_attrs, attrs)?;

    assert_eq!(left_exp.attributes, right_exp.attributes);

    let union = Union::new(
        &Box::new(left_exp.expression),
        &Box::new(right_exp.expression),
    );
    let raw = RawExpression::Union {
        left: left_exp.raw.boxed(),
        right: right_exp.raw.boxed(),
    };

    Ok(SubExpression::new(
        left_exp.attributes,
        left_exp.join_key, // irrelevant
        Mono::Union(union),
        raw,
    ))
}

/// Helper for `make_expression`.
fn expression(
    formula: &Formula,
    join_attr: &AttributeList,
    final_attr: &AttributeList,
) -> Result<SubExpression> {
    match formula {
        Formula::Bottom => Ok(SubExpression::new(
            Vec::new().into(),
            |t: &Tuple| t.clone(),
            Mono::Empty(Empty::new()),
            RawExpression::Empty,
        )),
        Formula::Top => Ok(SubExpression::new(
            Vec::new().into(),
            |t: &Tuple| t.clone(),
            Mono::Singleton(Singleton(vec![].into())),
            RawExpression::Full,
        )),
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
pub(super) fn make_expression(
    formula: &Formula,
    attributes: &AttributeList,
) -> Result<Mono<Tuple>> {
    expression(formula, &Vec::new().into(), attributes).map(SubExpression::into_expression)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chase::E;
    use razor_fol::{formula, v};
    use relalg::{relalg, Database, Tuples};
    use std::convert::TryFrom;

    macro_rules! atts {
        ($vs:expr) => {{
            let vs: Result<Vec<_>> = $vs.iter().map(|v| Attribute::try_from(v)).collect();
            AttributeList::from(vs.unwrap())
        }};
    }

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
            let result = expression(&formula, &atts!(vec![]), &atts!(vec![v!(x)]))?;
            let tuples = db.evaluate(&result.expression)?;

            assert!(matches!(result.expression, Mono::Relation(_)));
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!(P(x));
            let result = expression(&formula, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))?;
            let tuples = db.evaluate(&result.expression)?;

            assert!(matches!(result.expression, Mono::Relation(_)));
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!(Q(x, y));
            let result = expression(&formula, &vec![].into(), &atts!(vec![v!(x), v!(y)]))?;
            let tuples = db.evaluate(&result.expression)?;

            assert!(matches!(result.expression, Mono::Relation(_)));
            assert_eq!(
                Tuples::from(vec![
                    vec![E(20), E(200)],
                    vec![E(30), E(300)],
                    vec![E(40), E(400)],
                ]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = formula!(Q(x, y));
            let result = expression(
                &formula,
                &atts!(vec![v!(x), v!(y)]),
                &atts!(vec![v!(y), v!(x)]),
            )?;
            let tuples = db.evaluate(&result.expression)?;

            assert!(matches!(result.expression, Mono::Project(_)));
            assert_eq!(
                Tuples::from(vec![
                    vec![E(200), E(20)],
                    vec![E(300), E(30)],
                    vec![E(400), E(40)],
                ]),
                tuples
            );
            assert_eq!(atts!(vec![v!(y), v!(x)]), result.attributes);
        }
        {
            let formula = formula!(Q(x, y));
            let result = expression(&formula, &atts!(vec![v!(x)]), &atts!(vec![v!(x), v!(x)]))?;
            let tuples = db.evaluate(&result.expression)?;

            assert!(matches!(result.expression, Mono::Project(_)));
            assert_eq!(
                Tuples::from(vec![
                    vec![E(20), E(20)],
                    vec![E(30), E(30)],
                    vec![E(40), E(40)],
                ]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x), v!(x)]), result.attributes);
        }

        Ok(())
    }

    #[test]
    fn test_and() -> Result<()> {
        let db = setup_database()?;
        {
            let formula = formula!([P(x)] & [R(y, z)]);
            let result = expression(&formula, &atts!(vec![]), &atts!(vec![v!(x), v!(y), v!(z)]))?;

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
            assert_eq!(atts!(vec![v!(x), v!(y), v!(z)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [R(y, x)]);
            let result = expression(&formula, &atts!(vec![]), &atts!(vec![v!(x), v!(y)]))?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(Tuples::from(vec![]), tuples);
            assert_eq!(atts!(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [R(x, y)]);
            let result = expression(&formula, &atts!(vec![v!(y)]), &atts!(vec![v!(x), v!(y)]))?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(2), E(20)], vec![E(3), E(30)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [Q(y, z)]);
            let result = expression(&formula, &atts!(vec![v!(x), v!(y)]), &atts!([v!(y), v!(x)]))?;

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
            assert_eq!(atts!(vec![v!(y), v!(x)]), result.attributes);
        }
        {
            let formula = formula!([P(x)] & [Q(y, z)]);
            let result = expression(
                &formula,
                &atts!(vec![v!(y), v!(x)]),
                &atts!(vec![v!(x), v!(y)]),
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
            assert_eq!(atts!(vec![v!(x), v!(y)]), result.attributes);
        }

        Ok(())
    }

    #[test]
    fn test_union() -> Result<()> {
        let db = setup_database()?;
        {
            let formula = formula!([Q(x, y)] | [R(y, x)]);
            let result = expression(&formula, &atts!(vec![]), &atts!(vec![v!(x), v!(y)]))?;

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
            assert_eq!(atts!(vec![v!(x), v!(y)]), result.attributes);
        }

        {
            let formula = formula!([Q(x, y)] | [R(y, x)]);
            let result = expression(&formula, &atts!(vec![]), &atts!(vec![v!(y)]))?;

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
            assert_eq!(atts!(vec![v!(y)]), result.attributes);
        }

        Ok(())
    }

    #[test]
    fn test_formula() -> Result<()> {
        let db = setup_database()?;
        {
            let formula = formula!({ [P(x)] & [P(x)] } & { P(x) });
            let result = expression(&formula, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y)] });
            let result = expression(&formula, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))?;

            let tuples = db.evaluate(&result.expression)?;
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x)]), result.attributes);
        }
        {
            let formula = formula!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y, z)] });
            let result = expression(
                &formula,
                &atts!(vec![v!(z)]),
                &atts!(vec![v!(y), v!(x), v!(z)]),
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
            assert_eq!(atts!(vec![v!(y), v!(x), v!(z)]), result.attributes);
        }
        Ok(())
    }
}
