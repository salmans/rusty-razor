//*! Implements the algorithm for converting a relational formula to a relational expression in `codd`.*/
use super::{
    attribute::{Attribute, AttributeList},
    Error, Tuple,
};
use codd::expression::{Empty, Expression, Mono, Relation, Singleton};
use either::Either;
use razor_fol::{
    syntax::{
        formula::{Atom, Atomic, Equals},
        term::Variable,
        Formula, EQ_SYM,
    },
    transform::{FlatClause, Relational},
};
use std::collections::HashMap;

// Internal types for iterating over a formula of type `Relational`
type Literal = Atomic<Variable>;
type Clause<'a> = &'a [Literal];
type ClauseSet<'a> = &'a [Clause<'a>];

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

// Represents the recursive structure of a relation expression as it is constructed.
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

// Is the trait of objects that map a tuple to another.
trait TupleMap: FnMut(&Tuple) -> Tuple + 'static {}
impl<F: FnMut(&Tuple) -> Tuple + 'static> TupleMap for F {}

impl AttributeList {
    /// Makes a `TupleMap` closure that given a `Tuple` over the attributes of `self`,
    /// returns a `Tuple` projected by `attributes`.
    fn project(&self, attributes: &AttributeList) -> impl TupleMap {
        let mut key_indices = Vec::new();
        for v in attributes.attributes() {
            key_indices.push(self.iter().position(|item| item == v).unwrap());
        }

        move |t: &Tuple| key_indices.iter().map(|i| t[*i]).collect()
    }
}

// Represents a relational expression of type `Mono<Tuple>` while the expression
// is being constructed.
struct SubExpression {
    // Is the attributes associated to this expression.
    attributes: AttributeList,

    // Maps a tuple of `expression` to the keys that are used to join this subexpression with
    // another subexpression at the upper level of the expression tree.
    join_key: Box<dyn TupleMap>,

    // Is the (sub)expression in the context of a larger expression.
    expression: Mono<Tuple>,

    // Returns a "raw" representation of the sub-expression, which can identify the sub-exprewssion.
    raw: RawExpression,
}

impl SubExpression {
    // Creates a new subexpression instance.
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

    // Creates an instance corresponding to a full subexpression (logical truth).
    fn full() -> Self {
        Self::new(
            AttributeList::empty(),
            |_: &Tuple| unreachable!(),
            Mono::from(Singleton::new(vec![])),
            RawExpression::Full,
        )
    }

    // Creates an instance corresponding to an empty subexpression (logical falsehood).
    fn empty() -> Self {
        Self::new(
            AttributeList::empty(),
            |_: &Tuple| unreachable!(),
            Mono::from(Empty::new()),
            RawExpression::Empty,
        )
    }

    // Returns the `self`'s `expression`.
    fn expression(&self) -> &Mono<Tuple> {
        &self.expression
    }

    fn set_expression(&mut self, expression: Mono<Tuple>) {
        self.expression = expression;
    }

    /// Returns the `self`'s `raw` expression.
    fn raw(&self) -> &RawExpression {
        &self.raw
    }

    /// Consumes `self` and returns its `expression`.
    fn into_mono(self) -> Mono<Tuple> {
        self.expression
    }
}

/// Converts compatible relationalized first-order formulae of type [`Relational`] to
/// relational query expressions in `codd`.
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
        rel: &Relational,
        attributes: &AttributeList,
    ) -> Result<Mono<Tuple>, Error> {
        use itertools::Itertools;

        self.clause_set(
            &rel.iter().map(FlatClause::literals).collect_vec(),
            &AttributeList::new(vec![]),
            attributes,
        )
        .map(SubExpression::into_mono)
    }

    // Memoizes `sub_expr` if `self` is a memoizing instance.
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

    fn atomic(
        &mut self,
        atomic: &Literal,
        key_attrs: &AttributeList,
        attrs: &AttributeList,
    ) -> Result<SubExpression, Error> {
        match atomic {
            Atomic::Atom(this) => self.atom(this, key_attrs, attrs),
            Atomic::Equals(this) => self.equals(this, key_attrs, attrs),
        }
    }

    // Creates a relational expression (projection over an instance) for an [`Atom`].
    // `key_attrs` is the expected key attributes for joining the resulting subexpression
    // with the subexpression at the upper level in the expression tree.
    // `attrs` is the expected attributes of the resulting subexpression.
    fn atom(
        &mut self,
        atom: &Atom<Variable>,
        key_attrs: &AttributeList,
        attrs: &AttributeList,
    ) -> Result<SubExpression, Error> {
        let (expr_attrs, expr_indices) = attributes_and_indices(attrs, &atom.terms)?;

        let to_project = attrs.len() != atom.terms.len()
            || expr_indices
                .iter()
                .zip(0..atom.terms.len())
                .any(|(x, y)| *x != y);

        // The db instance containing tuples of `pred` is identified by `pred.to_string()`:
        let instance: Mono<Tuple> = Relation::new(&atom.predicate.to_string()).into();

        // `join_key` transforms a tuple to its expected keys:
        let key = expr_attrs.project(&key_attrs);

        let relation = RawExpression::Relation(atom.predicate.to_string());
        let result = if to_project {
            let raw = RawExpression::Project {
                expression: relation.boxed(),
                indices: expr_indices.iter().map(|&i| i as u8).collect(),
            };
            // Project only the expected attributes of the instance:
            let expr = instance
                .builder()
                .project(move |p| expr_indices.iter().map(|i| p[*i]).collect())
                .build()
                .into();
            let mut result = SubExpression::new(expr_attrs, key, expr, raw);
            self.memoize(&mut result)?;
            result
        } else {
            // optimizing identity projection:
            SubExpression::new(expr_attrs, key, instance, relation)
        };

        Ok(result)
    }

    // Similar to `Convertor::atom()` but works for positive equality literals of type `Equals`.
    fn equals(
        &mut self,
        equals: &Equals<Variable>,
        key_attrs: &AttributeList,
        attrs: &AttributeList,
    ) -> Result<SubExpression, Error> {
        // `equals.left` is at index 0 and `equals.right` at index 1:
        let (expr_attrs, expr_indices) =
            attributes_and_indices(attrs, &[equals.left.clone(), equals.right.clone()])?;

        let to_project = attrs.len() != 2 || expr_indices != [0, 1];

        let instance: Mono<Tuple> = Relation::new(EQ_SYM).into();

        // `join_key` transforms a tuple to its expected keys:
        let key = expr_attrs.project(&key_attrs);

        let relation = RawExpression::Relation(EQ_SYM.into());
        let result = if to_project {
            let raw = RawExpression::Project {
                expression: relation.boxed(),
                indices: expr_indices.iter().map(|&i| i as u8).collect(),
            };
            // Project only the expected attributes of the instance:
            let expr = instance
                .builder()
                .project(move |p| expr_indices.iter().map(|i| p[*i]).collect())
                .build()
                .into();
            let mut result = SubExpression::new(expr_attrs, key, expr, raw);
            self.memoize(&mut result)?;
            result
        } else {
            // optimizing identity projection:
            SubExpression::new(expr_attrs, key, instance, relation)
        };

        Ok(result)
    }

    // Creates nested relational join expressions for a relational clause, corresponding to
    // conjunction of positive literals.
    // `key_attrs` is the expected key attributes for joining the resulting subexpression
    // with the subexpression at the upper level in the expression tree.
    // `attrs` is the expected attributes of the resulting subexpression.
    fn clause(
        &mut self,
        clause: Clause,
        key_attrs: &AttributeList,
        attrs: &AttributeList,
    ) -> Result<SubExpression, Error> {
        use std::convert::TryFrom;

        match clause {
            [] => Ok(SubExpression::full()),
            [atomic] => self.atomic(atomic, key_attrs, attrs),
            [first, rest @ ..] => {
                let left_attrs = AttributeList::new(
                    first
                        .free_vars()
                        .into_iter()
                        .map(Attribute::try_from)
                        .collect::<Result<Vec<_>, _>>()?,
                );
                let right_attrs = AttributeList::new(
                    rest.iter()
                        .flat_map(|v| v.free_vars())
                        .into_iter()
                        .map(Attribute::try_from)
                        .collect::<Result<Vec<_>, _>>()?,
                );

                let common_attrs = left_attrs.intersect(&right_attrs); // join key attributes of left and right
                let left_sub = self.atomic(first, &common_attrs, &attrs.union(&right_attrs))?;
                let right_sub =
                    self.clause(rest, &common_attrs, &attrs.union(&left_sub.attributes))?;

                let mut expr_attrs = Vec::new(); // attributes of the resulting expression
                let mut expr_indices = Vec::new(); // indices of those attributes
                for attr in attrs.iter() {
                    let mut left_iter = left_sub.attributes.iter();
                    let mut right_iter = right_sub.attributes.iter();

                    // Is an expected attribute in the left or the right expression?
                    if let Some(p) = left_iter.position(|item| item == attr) {
                        expr_indices.push(Either::Left(p));
                        expr_attrs.push(attr.clone());
                    } else if let Some(p) = right_iter.position(|item| item == attr) {
                        expr_indices.push(Either::Right(p));
                        expr_attrs.push(attr.clone());
                    }
                }

                let expr_attrs = AttributeList::new(expr_attrs);
                let join_key = expr_attrs.project(&key_attrs); // join key for the expression on top
                let raw = RawExpression::join(
                    left_sub.raw,
                    right_sub.raw,
                    expr_indices.iter().map(|e| e.map(|i| i as u8)).collect(),
                );

                let join = left_sub
                    .expression
                    .builder()
                    .with_key(left_sub.join_key)
                    .join(right_sub.expression.builder().with_key(right_sub.join_key))
                    .on(move |_, l, r| {
                        expr_indices
                            .iter()
                            .map(|i| i.either(|i| l[i], |i| r[i]))
                            .collect()
                    })
                    .build();

                let mut result = SubExpression::new(expr_attrs, join_key, join.into(), raw);
                self.memoize(&mut result)?;

                Ok(result)
            }
        }
    }

    // Creates nested relational union expressions for a relational clause set, corresponding to
    // disjunction of positive relational clauses.
    // `key_attrs` is the expected key attributes for joining the resulting subexpression with
    // the subexpression at the upper level in the expression tree.
    // `attrs` is the expected attributes of the resulting subexpression.
    fn clause_set(
        &mut self,
        clause_set: ClauseSet,
        key_attrs: &AttributeList,
        attrs: &AttributeList,
    ) -> Result<SubExpression, Error> {
        match clause_set {
            [] => Ok(SubExpression::empty()),
            [clause] => self.clause(&clause, key_attrs, attrs),
            [first, rest @ ..] => {
                // Disjuctions simply hope that left and right have the same attributes:
                let left_exp = self.clause(first, key_attrs, attrs)?;
                let right_exp = self.clause_set(rest, key_attrs, attrs)?;
                assert_eq!(left_exp.attributes, right_exp.attributes);

                let union = left_exp
                    .expression
                    .builder()
                    .union(right_exp.expression)
                    .build();
                let raw = RawExpression::union(left_exp.raw, right_exp.raw);

                let mut result = SubExpression::new(
                    left_exp.attributes,
                    left_exp.join_key, // irrelevant
                    Mono::from(union),
                    raw,
                );
                self.memoize(&mut result)?;

                Ok(result)
            }
        }
    }
}

impl<'d> Default for Convertor<'d> {
    fn default() -> Self {
        Self::new()
    }
}

// Converts a slice of `Variable`s to attributes where they overlap with a `target` list
// of attributes and returns the resulting `AttributeList` together with the indices of
// the matching variables.
fn attributes_and_indices(
    target: &AttributeList,
    vars: &[Variable],
) -> Result<(AttributeList, Vec<usize>), Error> {
    use std::convert::TryFrom;

    let var_attrs = vars
        .iter()
        .map(|t| Attribute::try_from(t.symbol()))
        .collect::<Result<Vec<_>, _>>()?;

    let mut expr_attrs = Vec::new(); // attributes of the resulting expression
    let mut expr_indices = Vec::new(); // positions of those attributes in the tuple
    target.iter().for_each(|attr| {
        let mut vars_iter = var_attrs.iter();
        if let Some(p) = vars_iter.position(|item| item == attr) {
            expr_indices.push(p);
            expr_attrs.push(attr.clone());
        }
    });

    Ok((AttributeList::new(expr_attrs), expr_indices))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chase::E;
    use codd::{query, Database, Tuples};
    use itertools::Itertools;
    use razor_fol::{fof, syntax::FOF, v};
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
            let original = convertor.convert(&relational($fmla), &$atts).unwrap();
            let memoized = memo.convert(&relational($fmla), &$atts).unwrap();

            if $is_memoized {
                assert!(matches!(memoized, Mono::View(_)));
                let rememoized = memo.convert(&relational($fmla), &$atts).unwrap();
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

    // Assumes the input in GNF
    fn relational(fof: FOF) -> Relational {
        use razor_fol::transform::{PcfSet, ToRelational};

        PcfSet::try_from(fof).unwrap().relational()
    }

    #[test]
    fn test_atom() {
        let db = setup_database().unwrap();
        {
            let formula = fof!(P(x));
            let mut convertor = Convertor::new();
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![]), &atts!(vec![v!(x)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(
                    &clauses,
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(
                    &clauses,
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![v!(x)]), &atts!(vec![v!(x), v!(x)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![]), &atts!(vec![v!(x), v!(y), v!(z)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![]), &atts!(vec![v!(x), v!(y)]))
                .unwrap();

            let tuples = db.evaluate(&result.expression).unwrap();
            assert_eq!(Tuples::from(vec![]), tuples);
            assert_eq!(atts!(vec![v!(x), v!(y)]), result.attributes);
        }
        {
            let formula = fof!([P(x)] & [R(x, y)]);
            let mut convertor = Convertor::new();
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![v!(y)]), &atts!(vec![v!(x), v!(y)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![v!(x), v!(y)]), &atts!([v!(y), v!(x)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(
                    &clauses,
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![]), &atts!(vec![v!(x), v!(y)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![]), &atts!(vec![v!(y)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(&clauses, &atts!(vec![v!(x)]), &atts!(vec![v!(x)]))
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
            let relational = relational(formula);
            let clauses = relational.iter().map(FlatClause::literals).collect_vec();

            let result = convertor
                .clause_set(
                    &clauses,
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
            false
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
