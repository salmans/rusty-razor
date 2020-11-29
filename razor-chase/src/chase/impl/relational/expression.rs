//*! Implements the algorithm for converting a relational formula to a relational expression in `codd`.*/
use super::{
    attribute::{Attribute, AttributeList},
    Error, Tuple,
};
use codd::expression::{Empty, Expression, Mono, Relation, Singleton};
use either::Either;
use itertools::Itertools;
use razor_fol::syntax::{Formula, Pred, FOF};
use std::collections::HashMap;

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
struct RawJoin {
    left: RawExpression,
    right: RawExpression,
    indices: Vec<Either<u8, u8>>,
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
struct RawUnion {
    left: RawExpression,
    right: RawExpression,
}

/// Represents the recursive structure of a relation expression as it is constructed.
#[derive(PartialEq, Eq, Clone, Hash, Debug)]
enum RawExpression {
    Full,
    Empty,
    Relation(String),
    Project {
        expression: Box<RawExpression>,
        indices: Vec<u8>,
    },
    Join(Box<RawJoin>),
    Union(Box<RawUnion>),
}

impl RawExpression {
    fn join(left: RawExpression, right: RawExpression, indices: Vec<Either<u8, u8>>) -> Self {
        Self::Join(Box::new(RawJoin {
            left,
            right,
            indices,
        }))
    }

    fn union(left: RawExpression, right: RawExpression) -> Self {
        Self::Union(Box::new(RawUnion { left, right }))
    }

    fn boxed(self) -> Box<Self> {
        Box::new(self)
    }
}

/// Is the trait of objects that map a tuple to another.
trait TupleMap: FnMut(&Tuple) -> Tuple + 'static {}
impl<F: FnMut(&Tuple) -> Tuple + 'static> TupleMap for F {}

impl AttributeList {
    /// Makes a `TupleMap` closure that given a `Tuple` over the attributes of the receiver,
    /// returns a `Tuple` projected by `attributes`.
    fn project(&self, attributes: &AttributeList) -> impl TupleMap {
        let mut key_indices = Vec::new();
        for v in attributes.attributes() {
            key_indices.push(self.iter().position(|item| item == v).unwrap());
        }

        move |t: &Tuple| key_indices.iter().map(|i| t[*i]).collect()
    }
}

/// Represents a relational expression of type `Mono<Tuple>` while the expression
/// is being constructed.
struct SubExpression {
    /// Is the attributes associated to this expression.
    attributes: AttributeList,

    /// Maps a tuple of `expression` to the keys that are used to join this subexpression with
    /// another subexpression at the upper level of the expression tree.
    join_key: Box<dyn TupleMap>,

    /// Is the (sub)expression in the context of a larger expression.
    expression: Mono<Tuple>,

    /// Returns a "raw" representation of the sub-expression, which can identify the sub-exprewssion.
    raw: RawExpression,
}

impl SubExpression {
    fn new(
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

    /// Returns the receiver's `expression`.
    fn expression(&self) -> &Mono<Tuple> {
        &self.expression
    }

    fn set_expression(&mut self, expression: Mono<Tuple>) {
        self.expression = expression;
    }

    /// Returns the receiver's `raw` expression.
    fn raw(&self) -> &RawExpression {
        &self.raw
    }

    /// Consumes the receiver and returns its `expression`.
    fn into_expression(self) -> Mono<Tuple> {
        self.expression
    }
}

/// Converts compatible relationalized first-order formulae to relational expressions
/// in `codd`.
pub(super) struct Convertor<'d> {
    views: HashMap<RawExpression, Mono<Tuple>>,
    database: Option<&'d mut codd::Database>,
}

impl<'d> Convertor<'d> {
    /// Creates a new non-memoizing instance of the `Convertor`.
    pub fn new() -> Self {
        Self {
            views: HashMap::new(),
            database: None,
        }
    }

    /// Creates a new memoizing instance of `Convertor`. The memoizing convertor
    /// agressively adds materialized views to `database` for every expression it converts
    /// and uses them when converting future expressions.
    pub fn memoizing(database: &'d mut codd::Database) -> Self {
        Self {
            views: HashMap::new(),
            database: Some(database),
        }
    }

    /// Converts `formula` to a relational expression in `codd` with `attributes` as the
    /// relational expression attributes.
    pub fn convert(
        &mut self,
        formula: &FOF,
        attributes: &AttributeList,
    ) -> Result<Mono<Tuple>, Error> {
        self.expression(formula, &AttributeList::new(vec![]), attributes)
            .map(SubExpression::into_expression)
    }

    /// Memoizes `sub_expr` if the receiver is a memoizing instance.
    fn memoize(&mut self, sub_expr: &mut SubExpression) -> Result<(), codd::Error> {
        if let Some(database) = &mut self.database {
            if !self.views.contains_key(sub_expr.raw()) {
                let expr = sub_expr.expression().clone();
                let view = database.store_view(expr)?;
                let entry = Mono::from(view);
                self.views.insert(sub_expr.raw().clone(), entry.clone());
                sub_expr.set_expression(entry);
            }
        }
        Ok(())
    }

    /// Creates a relational expression (projection over an instance) for a predicate `pred` applied
    /// to a list of variables `vars`. `key_attrs` is the expected key attributes for joining the
    /// resulting subexpression with the subexpression at the upper level in the expression tree.
    /// `attrs` is the expected attributes of the resulting subexpression.
    fn atomic_expression(
        &self,
        pred: &Pred,
        vars: &[razor_fol::syntax::V],
        key_attrs: &AttributeList,
        attrs: &AttributeList,
    ) -> Result<SubExpression, Error> {
        use std::convert::TryFrom;

        let vars = vars
            .iter()
            .map(Attribute::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        let mut expr_attrs = Vec::new(); // attributes of the resulting expression
        let mut expr_indices = Vec::new(); // positions of those attributes in the tuple

        for attr in attrs.iter() {
            let mut vars_iter = vars.iter();
            if let Some(p) = vars_iter.position(|item| item == attr) {
                expr_indices.push(p);
                expr_attrs.push(attr.clone());
            }
        }

        let is_projected = attrs.len() != vars.len()
            || expr_indices.iter().zip(0..vars.len()).any(|(x, y)| *x != y);

        // The database instance containing tuples of `pred` is identified by `pred.to_string()`:
        let instance: Mono<Tuple> = Relation::new(&pred.to_string()).into();
        let expr_attrs = AttributeList::new(expr_attrs);

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
            instance
                .builder()
                .project(move |p| expr_indices.iter().map(|i| p[*i]).collect())
                .build()
                .into()
        } else {
            instance
        };

        Ok(SubExpression::new(expr_attrs, key, expr, raw))
    }

    /// Creates a join expression for the conjunction of `left` and `right`.
    /// `key_attrs` is the expected key attributes for joining the
    /// resulting subexpression with the subexpression at the upper level in the expression tree.
    /// `attrs` is the expected attributes of the resulting subexpression.
    fn and_expression(
        &mut self,
        left: &FOF,
        right: &FOF,
        key_attrs: &AttributeList,
        attrs: &AttributeList,
    ) -> Result<SubExpression, Error> {
        use std::convert::TryFrom;

        let left_attrs = AttributeList::new(
            left.free_vars()
                .into_iter()
                .map(Attribute::try_from)
                .collect::<Result<Vec<_>, _>>()?,
        );
        let right_attrs = AttributeList::new(
            right
                .free_vars()
                .into_iter()
                .map(Attribute::try_from)
                .collect::<Result<Vec<_>, _>>()?,
        );

        let common_vars = left_attrs.intersect(&right_attrs); // join key attributes of left and right
        let left_sub = self.expression(left, &common_vars, &attrs.union(&right_attrs))?;
        let right_sub = self.expression(right, &common_vars, &attrs.union(&left_sub.attributes))?;

        let mut expr_attrs = Vec::new(); // attributes of the resulting expression
        let mut expr_indices = Vec::new(); // indices of those attributes

        for v in attrs.iter() {
            let mut left_iter = left_sub.attributes.iter();
            let mut right_iter = right_sub.attributes.iter();

            // Is an expected attribute in the left or the right expression?
            if let Some(p) = left_iter.position(|item| item == v) {
                expr_indices.push(Either::Left(p));
                expr_attrs.push(v.clone());
            } else if let Some(p) = right_iter.position(|item| item == v) {
                expr_indices.push(Either::Right(p));
                expr_attrs.push(v.clone());
            }
        }

        let expr_attrs = AttributeList::new(expr_attrs);
        let join_key = expr_attrs.project(&key_attrs); // join key for the expression on top
        let raw = RawExpression::join(
            left_sub.raw,
            right_sub.raw,
            expr_indices.iter().map(|ei| ei.map(|i| i as u8)).collect(),
        );

        let left_key = left_sub.join_key;
        let left_exp = left_sub.expression;

        let right_key = right_sub.join_key;
        let right_exp = right_sub.expression;

        let join = left_exp
            .builder()
            .with_key(left_key)
            .join(right_exp.builder().with_key(right_key))
            .on(move |_, l, r| {
                expr_indices
                    .iter()
                    .map(|i| i.either(|i| l[i], |i| r[i]))
                    .collect()
            })
            .build();

        Ok(SubExpression::new(expr_attrs, join_key, join.into(), raw))
    }

    /// Creates a union expression for the disjunction of `left` and `right`.
    /// `key_attrs` is the expected key attributes for joining the
    /// resulting subexpression with the subexpression at the upper level in the expression tree.
    /// `attrs` is the expected attributes of the resulting subexpression.
    fn or_expression(
        &mut self,
        left: &FOF,
        right: &FOF,
        key_attrs: &AttributeList,
        attrs: &AttributeList,
    ) -> Result<SubExpression, Error> {
        // Disjuctions simply hope that left and right have the same attributes:
        let left_exp = self.expression(left, key_attrs, attrs)?;
        let right_exp = self.expression(right, key_attrs, attrs)?;

        assert_eq!(left_exp.attributes, right_exp.attributes);

        let union = left_exp
            .expression
            .builder()
            .union(right_exp.expression)
            .build();
        let raw = RawExpression::union(left_exp.raw, right_exp.raw);

        Ok(SubExpression::new(
            left_exp.attributes,
            left_exp.join_key, // irrelevant
            Mono::from(union),
            raw,
        ))
    }

    // A helper for `convert`.
    fn expression(
        &mut self,
        formula: &FOF,
        join_attr: &AttributeList,
        final_attr: &AttributeList,
    ) -> Result<SubExpression, Error> {
        match formula {
            FOF::Bottom => Ok(SubExpression::new(
                AttributeList::new(vec![]),
                |t: &Tuple| t.clone(),
                Mono::from(Empty::new()),
                RawExpression::Empty,
            )),
            FOF::Top => Ok(SubExpression::new(
                AttributeList::new(vec![]),
                |t: &Tuple| t.clone(),
                Mono::from(Singleton::new(vec![])),
                RawExpression::Full,
            )),
            FOF::Atom(this) => {
                let free_vars = formula.free_vars().into_iter().cloned().collect_vec();
                let mut sub =
                    self.atomic_expression(&this.predicate, &free_vars, &join_attr, &final_attr)?;
                if matches!(sub.raw(), RawExpression::Project {..}) {
                    self.memoize(&mut sub)?;
                }
                Ok(sub)
            }
            FOF::And(this) => {
                let mut sub =
                    self.and_expression(&this.left, &this.right, join_attr, final_attr)?;
                self.memoize(&mut sub)?;
                Ok(sub)
            }

            FOF::Or(this) => {
                let mut sub = self.or_expression(&this.left, &this.right, join_attr, final_attr)?;
                self.memoize(&mut sub)?;
                Ok(sub)
            }
            _ => Err(Error::BadRelationalFormula {
                formula: formula.clone(),
            }),
        }
    }
}

impl<'d> Default for Convertor<'d> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chase::E;
    use codd::{query, Database, Tuples};
    use razor_fol::{fof, v};
    use std::convert::TryFrom;

    macro_rules! atts {
        ($vs:expr) => {{
            let vs: Result<Vec<_>, _> = $vs.iter().map(|v| Attribute::try_from(v)).collect();
            AttributeList::new(vs.unwrap())
        }};
    }

    macro_rules! test_memo {
        ($fmla:expr, $atts: expr, $is_memoized:expr) => {{
            let mut db = setup_database().unwrap();
            let mut convertor = Convertor::new();
            let mut memo = Convertor::memoizing(&mut db);
            let original = convertor.convert(&$fmla, &$atts).unwrap();
            let memoized = memo.convert(&$fmla, &$atts).unwrap();

            if $is_memoized {
                assert!(matches!(memoized, Mono::View(_)));
                let rememoized = memo.convert(&$fmla, &$atts).unwrap();
                match (&memoized, &rememoized) {
                    (Mono::View(ref v1), Mono::View(ref v2)) => {
                        assert_eq!(format!("{:?}", v1), format!("{:?}", v2))
                    }
                    _ => {}
                }
            } else {
                assert!(matches!(memoized, Mono::Relation(_)));
            }

            let original_tuples = db.evaluate(&original).unwrap();
            let memoized_tuples = db.evaluate(&memoized).unwrap();
            assert_eq!(original_tuples, memoized_tuples);
        }};
    }

    fn setup_database() -> Result<Database, Error> {
        let mut db = Database::new();
        let p = query! { db, create relation "P":<Tuple> }.unwrap();
        let q = query! { db, create relation "Q":<Tuple> }.unwrap();
        let r = query! { db, create relation "R":<Tuple> }.unwrap();

        query! (db, insert into (p) values [vec![E(1)], vec![E(2)], vec![E(3)]]).unwrap();
        query! (db, insert into (q) values [vec![E(20), E(200)], vec![E(30), E(300)], vec![E(40), E(400)]]).unwrap();
        query! (db, insert into (r) values [vec![E(2), E(20)], vec![E(3), E(30)], vec![E(4), E(40)]]).unwrap();

        Ok(db)
    }

    #[test]
    fn test_atom() {
        let db = setup_database().unwrap();
        {
            let formula = fof!(P(x));
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![]), &atts!(vec![v!(x)]))
                .unwrap();
            let tuples = db.evaluate(&result.expression).unwrap();

            assert!(matches!(result.expression, Mono::Relation(_)));
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x)]), result.attributes);
        }
        {
            let formula = fof!(P(x));
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))
                .unwrap();
            let tuples = db.evaluate(&result.expression).unwrap();

            assert!(matches!(result.expression, Mono::Relation(_)));
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x)]), result.attributes);
        }
        {
            let formula = fof!(Q(x, y));
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(
                    &formula,
                    &AttributeList::new(vec![]),
                    &atts!(vec![v!(x), v!(y)]),
                )
                .unwrap();
            let tuples = db.evaluate(&result.expression).unwrap();

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
            let formula = fof!(Q(x, y));
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(
                    &formula,
                    &atts!(vec![v!(x), v!(y)]),
                    &atts!(vec![v!(y), v!(x)]),
                )
                .unwrap();
            let tuples = db.evaluate(&result.expression).unwrap();

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
            let formula = fof!(Q(x, y));
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![v!(x)]), &atts!(vec![v!(x), v!(x)]))
                .unwrap();
            let tuples = db.evaluate(&result.expression).unwrap();

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
    }

    #[test]
    fn test_atom_memoized() {
        test_memo!(fof!(P(x)), atts!(vec![v!(x)]), false);
        test_memo!(fof!(Q(x, y)), atts!(vec![v!(x), v!(y)]), false);
        test_memo!(fof!(Q(x, y)), atts!(vec![v!(y), v!(x)]), true);
        test_memo!(fof!(Q(x, y)), atts!(vec![v!(x), v!(x)]), true);
    }

    #[test]
    fn test_and() -> Result<(), Error> {
        let db = setup_database().unwrap();
        {
            let formula = fof!([P(x)] & [R(y, z)]);
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![]), &atts!(vec![v!(x), v!(y), v!(z)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
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
            let formula = fof!([P(x)] & [R(y, x)]);
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![]), &atts!(vec![v!(x), v!(y)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
            assert_eq!(Tuples::from(vec![]), tuples);
            assert_eq!(atts!(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = fof!([P(x)] & [R(x, y)]);
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![v!(y)]), &atts!(vec![v!(x), v!(y)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
            assert_eq!(
                Tuples::from(vec![vec![E(2), E(20)], vec![E(3), E(30)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = fof!([P(x)] & [Q(y, z)]);
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![v!(x), v!(y)]), &atts!([v!(y), v!(x)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
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
            let formula = fof!([P(x)] & [Q(y, z)]);
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(
                    &formula,
                    &atts!(vec![v!(y), v!(x)]),
                    &atts!(vec![v!(x), v!(y)]),
                )
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
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
    fn test_and_memoized() {
        test_memo!(
            fof!([P(x)] & [R(y, z)]),
            atts!(vec![v!(x), v!(y), v!(z)]),
            true
        );
        test_memo!(fof!([P(x)] & [R(y, x)]), atts!(vec![v!(x), v!(y)]), true);
        test_memo!(fof!([P(x)] & [R(x, y)]), atts!(vec![v!(x), v!(y)]), true);
        test_memo!(fof!([P(x)] & [Q(y, z)]), atts!(vec![v!(y), v!(x)]), true);
        test_memo!(fof!([P(x)] & [Q(y, z)]), atts!(vec![v!(x), v!(y)]), true);
    }

    #[test]
    fn test_or() -> Result<(), Error> {
        let db = setup_database().unwrap();
        {
            let formula = fof!([Q(x, y)] | [R(y, x)]);
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![]), &atts!(vec![v!(x), v!(y)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
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
            let formula = fof!([Q(x, y)] | [R(y, x)]);
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![]), &atts!(vec![v!(y)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
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
    fn test_or_memoized() {
        test_memo!(fof!([Q(x, y)] | [R(y, x)]), atts!(vec![v!(x), v!(y)]), true);
        test_memo!(fof!([Q(x, y)] | [R(y, x)]), atts!(vec![v!(y)]), true);
    }

    #[test]
    fn test_formula() {
        let db = setup_database().unwrap();
        {
            let formula = fof!({ [P(x)] & [P(x)] } & { P(x) });
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x)]), result.attributes);
        }
        {
            let formula = fof!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y)] });
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(&formula, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
            assert_eq!(
                Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)],]),
                tuples
            );
            assert_eq!(atts!(vec![v!(x)]), result.attributes);
        }
        {
            let formula = fof!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y, z)] });
            let mut convertor = Convertor::new();
            let result = convertor
                .expression(
                    &formula,
                    &atts!(vec![v!(z)]),
                    &atts!(vec![v!(y), v!(x), v!(z)]),
                )
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
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
    }

    #[test]
    fn test_formula_memoized() {
        test_memo!(
            fof!({ [P(x)] & [P(x)] } & { P(x) }),
            atts!(vec![v!(x)]),
            true
        );
        test_memo!(
            fof!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y)] }),
            atts!(vec![v!(x)]),
            true
        );
        test_memo!(
            fof!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y, z)] }),
            atts!(vec![v!(y), v!(x), v!(z)]),
            true
        );
    }
}
