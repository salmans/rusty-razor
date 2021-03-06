/*! Defines a relational formula and implements an algorithm for transforming compatible formula types
to [`Relational`].*/
use super::{PcfSet, PCF};
use crate::syntax::{
    formula::*,
    term::{Complex, Variable},
    Const, Error, Formula, Func, Pred, Sig, Var, FOF,
};
use itertools::Itertools;
use std::{collections::HashMap, iter::FromIterator, ops::Deref};

// Atomic formula over flat terms to build relational formulae
type FlatLiteral = Atomic<Variable>;

/// Consists of a list of [`Atomic`]s over flat terms of type [`Variable`], treated as an
/// ordered (multi-)set of literals. A [`FlatClause`] in interpreted as a conjunction of
/// literals.
///
/// **Note**: unlike [`Clause`] which is implemented by a [`BTreeSet`] of literals,
/// it is more convenient to process [`Relational`] formula as a vector of literals
/// that are topologically sorted (see [`ToRelational::relational`]).
///
/// [`Clause`]: crate::syntax::formula::clause::Clause
/// [`BTreeSet`]: std::collections::BTreeSet
#[derive(Clone, Debug)]
pub struct FlatClause(Vec<FlatLiteral>);

impl FlatClause {
    /// Returns the list of literals of `self`.
    pub fn literals(&self) -> &[FlatLiteral] {
        &self.0
    }

    /// Consumes `self` and returns its underlying list of literals.
    pub fn into_literals(self) -> Vec<FlatLiteral> {
        self.0
    }
}

impl Deref for FlatClause {
    type Target = [FlatLiteral];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<FlatLiteral> for FlatClause {
    fn from(value: FlatLiteral) -> Self {
        Self(vec![value])
    }
}

impl FromIterator<FlatLiteral> for FlatClause {
    fn from_iter<T: IntoIterator<Item = FlatLiteral>>(iter: T) -> Self {
        Self(Vec::from_iter(iter))
    }
}

impl IntoIterator for FlatClause {
    type Item = FlatLiteral;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl From<Vec<FlatLiteral>> for FlatClause {
    fn from(value: Vec<FlatLiteral>) -> Self {
        Self(value)
    }
}

impl Default for FlatClause {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl Formula for FlatClause {
    type Term = Variable;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::from_signatures(
            self.iter()
                .map(|l| l.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.0.iter().flat_map(|l| l.free_vars()).unique().collect()
    }

    fn transform_term(&self, f: &impl Fn(&Variable) -> Variable) -> Self {
        self.0.iter().map(|lit| lit.transform_term(f)).collect()
    }
}

impl From<FlatLiteral> for FOF {
    fn from(value: FlatLiteral) -> Self {
        match value {
            Atomic::Atom(this) => Atom::<Complex> {
                predicate: this.predicate,
                terms: this.terms.into_iter().map(|v| v.symbol().into()).collect(),
            }
            .into(),
            Atomic::Equals(this) => Equals {
                left: this.left.symbol().into(),
                right: this.right.symbol().into(),
            }
            .into(),
        }
    }
}

impl From<FlatClause> for FOF {
    fn from(value: FlatClause) -> Self {
        value
            .into_literals()
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

/// Represents a relational formula as a Disjunctive Normal Form (DNF) over positive
/// literals with flat terms. The primary use-case of this type is to transform
/// positive formulae in the head and body of a [`GNF`] to relational expressions
/// as database queries.
///
/// **Hint**: A relational formula contains only (flat) variable terms with
/// no functions nor constants.
///
/// [`GNF`]: crate::transform::GNF
#[derive(Clone, Debug)]
pub struct Relational(Vec<FlatClause>);

impl From<FlatClause> for Relational {
    fn from(value: FlatClause) -> Self {
        vec![value].into()
    }
}

impl FromIterator<FlatClause> for Relational {
    fn from_iter<T: IntoIterator<Item = FlatClause>>(iter: T) -> Self {
        Self(Vec::from_iter(iter))
    }
}

impl IntoIterator for Relational {
    type Item = FlatClause;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl From<Vec<FlatClause>> for Relational {
    fn from(value: Vec<FlatClause>) -> Self {
        Self(value)
    }
}

impl Relational {
    /// Returns the clauses of `self`.
    pub fn clauses(&self) -> &[FlatClause] {
        &self.0
    }

    /// Consumes `self` and returns its underlying clauses.
    pub fn into_clauses(self) -> Vec<FlatClause> {
        self.0
    }
}

impl Deref for Relational {
    type Target = [FlatClause];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Default for Relational {
    fn default() -> Self {
        Vec::<FlatClause>::new().into()
    }
}

struct FlatteningContext<'t, VG, CG, FG>
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    var_generator: &'t mut VG,
    const_generator: &'t mut CG,
    fn_generator: &'t mut FG,
}

impl<'t, VG, CG, FG> FlatteningContext<'t, VG, CG, FG>
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    fn new(
        var_generator: &'t mut VG,
        const_generator: &'t mut CG,
        fn_generator: &'t mut FG,
    ) -> Self {
        Self {
            var_generator,
            const_generator,
            fn_generator,
        }
    }

    #[inline(always)]
    fn next_var(&mut self) -> Var {
        (self.var_generator)()
    }

    #[inline(always)]
    fn const_pred(&mut self, c: &Const) -> Pred {
        (self.const_generator)(c)
    }

    #[inline(always)]
    fn fn_pred(&mut self, f: &Func) -> Pred {
        (self.fn_generator)(f)
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`Relational`].
pub trait ToRelational: Formula {
    /// Is similar to [`ToRelational::relational`] but uses custom closures for generating new symbols.
    ///
    /// **Example**:
    /// ```rust    
    /// # use razor_fol::syntax::{FOF, Const, Var, Func};
    /// # use std::convert::TryFrom;
    /// use razor_fol::transform::{GNF, ToRelational};
    ///
    /// let fof = "P(x) & Q(g(x)) -> (P(f(x)) & Q('c)) | R(x)".parse::<FOF>().unwrap();
    /// let gnf = GNF::try_from(fof).unwrap();
    ///
    /// // The body and head of a GNF can be relationalized:
    /// let gnf_body = gnf.body();
    /// let gnf_head = gnf.head();
    ///
    /// let mut var_counter = 0;
    /// let mut var_generator = || {
    ///     let name = var_counter.to_string();
    ///     var_counter += 1;
    ///     name.into()
    /// };
    /// let mut const_generator = |c: &Const| c.name().to_uppercase().into();
    /// let mut fn_generator = |f: &Func| f.name().to_uppercase().into();
    /// let body = gnf_body.relational_with(
    ///     &mut var_generator,
    ///     &mut const_generator,
    ///     &mut fn_generator
    /// );
    /// assert_eq!(
    ///     r"(P(x) ∧ G(x, 0)) ∧ Q(0)",
    ///     body.to_string()
    /// );    
    ///
    /// let head = gnf_head.relational_with(
    ///     &mut var_generator,
    ///     &mut const_generator,
    ///     &mut fn_generator
    /// );
    /// assert_eq!(
    ///     r"(((F(x, 1) ∧ P(1)) ∧ C(2)) ∧ Q(2)) ∨ R(x)",
    ///     head.to_string()
    /// );
    /// ```
    fn relational_with<VG, CG, FG>(
        &self,
        var_generator: &mut VG,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Relational
    where
        VG: FnMut() -> Var,
        CG: FnMut(&Const) -> Pred,
        FG: FnMut(&Func) -> Pred;

    /// Applies the relationalization algorithm on `self` and returns a relational formula.    
    ///
    /// **Note:**
    /// The underlying algorithm works on first-order formulae that are negation and quantifier-free:
    /// `¬`, `→`, `⇔`, `∃`, `∀` are not allowed as connectives. The transformation consists of applying
    /// the following rewrites on `self`:
    ///   * A constant `'c` rewrites to a predicate `C(x)`.
    ///   * A complex term `f(x_1, ..., x_n)` rewrites to a fresh variable `v` and an atomic
    /// formula `F(x_1, ..., x_n, v)` is conjoined with the input formula.
    ///
    /// In the resulting formula, the new (placeholder) variables are sorted topologically from
    /// left to right with the dependency between variables as the ordering relation as follows:
    /// A varialbe `v` depends on a variable `y` if and only if for a new function predicate, namely `F`,
    /// `F(..., y,..., v)` is a conjunct in the formula (i.e., the result of the
    /// function replaced by `F`, applied to its arguments, depends on `y`).
    ///
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// # use std::convert::TryFrom;
    /// use razor_fol::transform::{GNF, ToRelational};
    ///
    /// let fof = "P(x) -> P(f(x)) & Q('c)".parse::<FOF>().unwrap();
    /// let gnf = GNF::try_from(fof).unwrap();
    /// let gnf_head = gnf.head();
    /// let transformed = gnf_head.relational();
    /// assert_eq!(
    ///     r"(($f(x, ?0) ∧ P(?0)) ∧ @c(?1)) ∧ Q(?1)",
    ///     transformed.to_string()
    /// );
    /// ```
    fn relational(&self) -> Relational {
        let mut var_counter = 0;
        let mut var_generator = || {
            let name = format!("?{}", var_counter);
            var_counter += 1;
            name.into()
        };
        let mut const_generator = |c: &Const| format!("@{}", c.name()).into();
        let mut fn_generator = |f: &Func| format!("${}", f.name()).into();
        self.relational_with(&mut var_generator, &mut const_generator, &mut fn_generator)
    }
}

impl ToRelational for PCF {
    fn relational_with<VG, CG, FG>(
        &self,
        var_generator: &mut VG,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Relational
    where
        VG: FnMut() -> Var,
        CG: FnMut(&Const) -> Pred,
        FG: FnMut(&Func) -> Pred,
    {
        // keeping track of the generated variables to remove redundant equations later on:
        let mut generated_vars = Vec::new();
        let mut var_generator_ex = || {
            let v = var_generator();
            generated_vars.push(v.clone());
            v
        };
        let flattened = flatten_clause(
            self,
            &mut FlatteningContext::new(&mut var_generator_ex, const_generator, fn_generator),
        );
        let relational: Relational = flattened.into();
        simplify_equations(&relational, &mut generated_vars)
    }
}

impl ToRelational for PcfSet {
    fn relational_with<VG, CG, FG>(
        &self,
        var_generator: &mut VG,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Relational
    where
        VG: FnMut() -> Var,
        CG: FnMut(&Const) -> Pred,
        FG: FnMut(&Func) -> Pred,
    {
        // keeping track of the generated variables to remove redundant equations later on:
        let mut generated_vars = Vec::new();
        let mut var_generator_ex = || {
            let v = var_generator();
            generated_vars.push(v.clone());
            v
        };
        let flattened = flatten_clause_set(
            self,
            &mut FlatteningContext::new(&mut var_generator_ex, const_generator, fn_generator),
        );
        simplify_equations(&flattened, &mut generated_vars)
    }
}

impl Formula for Relational {
    type Term = Variable;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.0.iter().flat_map(|l| l.free_vars()).unique().collect()
    }

    fn transform_term(&self, f: &impl Fn(&Variable) -> Variable) -> Self {
        self.0
            .iter()
            .map(|clause| clause.transform_term(f))
            .collect()
    }
}

impl From<Relational> for FOF {
    fn from(value: Relational) -> Self {
        value
            .into_clauses()
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
    }
}

impl From<&Relational> for FOF {
    fn from(value: &Relational) -> Self {
        value.clone().into()
    }
}

impl std::fmt::Display for Relational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

// Recursively flattens a term and returns the resulting formula together with a placeholder
// variable for the term. Nothing needs to be done if the input term is a variable.
fn flatten_term<VG, CG, FG>(
    term: &Complex,
    context: &mut FlatteningContext<VG, CG, FG>,
) -> (Option<FlatClause>, Var)
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    match term {
        Complex::Var(v) => (None, v.clone()),
        Complex::Const(c) => {
            let var = context.next_var();
            let terms = vec![var.clone().into()];
            let predicate = context.const_pred(c);
            let atom = Atom { predicate, terms };
            (Some(vec![atom.into()].into()), var)
        }
        Complex::App { function, terms } => {
            let mut conjuncts = vec![];
            let mut terms = terms
                .iter()
                .map(|t| {
                    let (clauses, var) = flatten_term(t, context);
                    if let Some(cs) = clauses {
                        conjuncts.extend(cs.into_literals());
                    }
                    var.into()
                })
                .collect::<Vec<Variable>>();

            let var = context.next_var();
            terms.push(var.clone().into());

            let predicate = context.fn_pred(function);
            let atom = Atom { predicate, terms };

            // !!! This is preserving the topological order among variables:
            conjuncts.push(atom.into());
            (Some(conjuncts.into()), var)
        }
    }
}

// Applies top level flattening on the input clause set of type `PCFSet`.
fn flatten_clause_set<VG, CG, FG>(
    clause_set: &PcfSet,
    context: &mut FlatteningContext<VG, CG, FG>,
) -> Relational
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    clause_set
        .iter()
        .map(|clause| flatten_clause(clause, context))
        .collect()
}

// A helper to generate new flat variable terms and equations to extend the original formula.
fn make_equations<VG, CG, FG>(
    terms: &[Complex],
    context: &mut FlatteningContext<VG, CG, FG>,
) -> (Vec<Atomic<Variable>>, Vec<Variable>)
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    let mut conjuncts = Vec::new();
    let terms = terms
        .iter()
        .map(|t| {
            let (clauses, var) = flatten_term(t, context);
            if let Some(cs) = clauses {
                conjuncts.extend(cs.into_literals());
            }
            var.into()
        })
        .collect::<Vec<Variable>>();
    (conjuncts, terms)
}

// Applies top level flattening on the input clause set.
fn flatten_clause<VG, CG, FG>(
    clause: &PCF,
    context: &mut FlatteningContext<VG, CG, FG>,
) -> FlatClause
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    let clause = clause.iter().flat_map(|lit| match lit {
        Atomic::Atom(this) => {
            let (mut conjuncts, flat_terms) = make_equations(&this.terms, context);

            // !!! To preserve the topological order among variables,
            // append the new atom to the end:
            conjuncts.push(
                Atom {
                    predicate: this.predicate.clone(),
                    terms: flat_terms,
                }
                .into(),
            );
            conjuncts
        }
        Atomic::Equals(this) => {
            // left at index 0 and right at index 1:
            let (mut conjuncts, mut flat_terms) =
                make_equations(&[this.left.clone(), this.right.clone()], context);

            assert_eq!(2, flat_terms.len());
            let left = flat_terms.remove(0);
            let right = flat_terms.remove(0);

            // !!! To preserve the topological order among variables,
            // append the new equation to the end:
            conjuncts.push(Equals { left, right }.into());
            conjuncts
        }
    });
    clause.collect()
}

// As a helper for `simplify_equations` collects a set of rewrite rules as entries of a map, corresponding
// to equations with an existential variable on one side.
fn equation_rewrites<'a>(
    clause_set: &'a Relational,
    map: &mut HashMap<&'a Var, &'a Var>,
    generated_variables: &mut [Var],
) {
    clause_set.iter().for_each(|clause| {
        clause.iter().for_each(|atomic| {
            if let Atomic::Equals(this) = atomic {
                let left = &this.left;
                let right = &this.right;

                let l_generated = generated_variables.contains(left.symbol());
                let r_generated = generated_variables.contains(right.symbol());

                match (l_generated, r_generated) {
                    (false, true) => {
                        map.insert(right, left);
                    }
                    (true, false) => {
                        map.insert(left, right);
                    }
                    (true, true) => {
                        if map.contains_key(left.symbol()) {
                            map.insert(right, map.get(left.symbol()).unwrap());
                        } else if map.contains_key(right.symbol()) {
                            map.insert(left, map.get(right.symbol()).unwrap());
                        } else {
                            map.insert(left, right);
                        }
                    }
                    _ => {}
                }
            }
        });
    });
}

// Simplify tries to minimize the use of existential variables (generated by relationalize) by replacing
// them with universal or other existential variables that are syntactically equal with them.
// It also removes reflexive equations.
fn simplify_equations(clause_set: &Relational, generated_variables: &mut [Var]) -> Relational {
    let mut map = HashMap::new();
    equation_rewrites(clause_set, &mut map, generated_variables);

    let sub = |v: &Var| {
        let variable = map.get(v).map(|&t| t.clone()).unwrap_or_else(|| v.clone());
        Variable::from(variable)
    };

    clause_set
        .substitute(&sub)
        .into_clauses()
        .into_iter()
        .map(|clause| {
            clause
                .into_literals()
                .into_iter()
                // remove reflexive equations:
                .filter(|atomic| {
                    if let Atomic::Equals(this) = atomic {
                        this.left != this.right
                    } else {
                        true
                    }
                })
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transform::GNF;
    use std::convert::TryFrom;

    use crate::{
        assert_eq_sorted_vecs, fof,
        syntax::{signature::PredSig, Sig, EQ_SYM},
        term,
        transform::{ToGNF, PCF},
        v,
    };

    // Assumes the input in GNF
    fn clause_set(fof: FOF) -> Vec<PcfSet> {
        fof.gnf()
            .into_iter()
            .map(|f| f.into_body_and_head().1)
            .collect()
    }

    fn flatten(fof: FOF) -> String {
        let mut var_counter = 0;
        let mut var_generator = || {
            let name = format!("?{}", var_counter);
            var_counter += 1;
            name.into()
        };
        let mut const_generator = |c: &Const| format!("@{}", c.name()).into();
        let mut fn_generator = |f: &Func| format!("${}", f.name()).into();

        let rels = clause_set(fof)
            .iter()
            .map(|f| {
                flatten_clause_set(
                    f,
                    &mut FlatteningContext::new(
                        &mut var_generator,
                        &mut const_generator,
                        &mut fn_generator,
                    ),
                )
            })
            .map(FOF::from)
            .collect::<Vec<_>>();
        format!("{:?}", rels)
    }

    #[test]
    fn test_flatten() {
        assert_eq! {
            "[]",
            flatten(fof!('|')),
        };

        assert_eq! {
            "[false]",
            flatten(fof!(_|_)),
        };

        assert_eq! {
            "[P()]",
            flatten(fof!(P())),
        };
        assert_eq! {
            "[P(x, y)]",
            flatten(fof!(P(x, y))),
        };
        assert_eq! {
            "[x = y]",
            flatten(fof!((x) = (y))),
        }

        assert_eq! {
            "[@c(?0) & x = ?0]",
            flatten(fof!((x) = (@c))),
        }
        assert_eq! {
            "[(@c(?0) & @d(?1)) & ?0 = ?1]",
            flatten(fof!((@c) = (@d))),
        }
        assert_eq! {
            "[@c(?0) & P(?0)]",
            flatten(fof!(P(@c))),
        };
        assert_eq! {
            "[@c(?0) & P(x, ?0)]",
            flatten(fof!(P(x, @c))),
        };
        assert_eq! {
            "[(@c(?0) & @d(?1)) & P(?0, ?1)]",
            flatten(fof!(P(@c, @d))),
        };
        assert_eq! {
            "[$f(x, ?0) & P(?0)]",
            flatten(fof!(P(f(x)))),
        };
        assert_eq! {
            "[($g(x, ?0) & $f(?0, ?1)) & P(?1)]",
            flatten(fof!(P(f(g(x))))),
        };
        assert_eq! {
            "[(($g(x, ?0) & $f(?0, ?1)) & $f(y, ?2)) & P(?1, ?2)]",
            flatten(fof!(P(f(g(x)), f(y)))),
        };
        assert_eq! {
            "[P(x), Q(y)]",
            flatten(fof!((P(x)) & (Q(y)))),
        };
        assert_eq! {
            "[@c(?0) & P(?0), @d(?1) & Q(?1)]",
            flatten(fof!((P(@c)) & (Q(@d)))),
        };
        assert_eq! {
            "[P(x) | Q(y)]",
            flatten(fof!((P(x)) | (Q(y)))),
        };
        assert_eq! {
            "[(@c(?0) & P(?0)) | (@d(?1) & Q(?1))]",
            flatten(fof!((P(@c)) | (Q(@d)))),
        };
    }

    #[test]
    fn test_relationalize() {
        use crate::{syntax::formula::*, term};
        {
            let clause_set = PcfSet::from(vec![PCF::from(Equals {
                left: term!(f(x)),
                right: term!(y),
            })]);
            assert_eq!("$f(x, y)", clause_set.relational().to_string());
        }
        {
            let clause_set = PcfSet::from(vec![PCF::from(Equals {
                left: term!(f(x)),
                right: term!(g(y)),
            })]);
            assert_eq!("$f(x, ?1) ∧ $g(y, ?1)", clause_set.relational().to_string());
        }
        {
            let clause_set = PcfSet::from(vec![
                PCF::from(Equals {
                    left: term!(f(x)),
                    right: term!(g(y)),
                }),
                PCF::from(Equals {
                    left: term!(f(x)),
                    right: term!(y),
                }),
            ]);
            assert_eq!(
                "$f(x, y) ∨ ($f(x, ?2) ∧ $g(y, ?2))",
                clause_set.relational().to_string()
            );
        }
        {
            let clause_set = PcfSet::from(vec![PCF::from(Atom {
                predicate: Pred::from("P"),
                terms: vec![term!(x), term!(f(y))],
            })]);
            assert_eq!("$f(y, ?0) ∧ P(x, ?0)", clause_set.relational().to_string());
        }
        {
            let clause_set = PcfSet::from(vec![PCF::from(Atom {
                predicate: Pred::from("P"),
                terms: vec![term!(x), term!(f(x))],
            })]);
            assert_eq!("$f(x, ?0) ∧ P(x, ?0)", clause_set.relational().to_string());
        }
        {
            let clause_set = PcfSet::from(vec![PCF::from(Equals {
                left: term!(f(x)),
                right: term!(f(x)),
            })]);
            assert_eq!("$f(x, ?1) ∧ $f(x, ?1)", clause_set.relational().to_string());
        }
        {
            let clause_set = PcfSet::from(vec![PCF::from(vec![
                Atom {
                    predicate: Pred::from("P"),
                    terms: vec![term!(f(x, y))],
                }
                .into(),
                Atom {
                    predicate: Pred::from("Q"),
                    terms: vec![term!(f(x, y))],
                }
                .into(),
            ])]);
            assert_eq!(
                "(($f(x, y, ?0) ∧ P(?0)) ∧ $f(x, y, ?1)) ∧ Q(?1)",
                clause_set.relational().to_string()
            );
        }
        {
            let clause_set = PcfSet::from(vec![
                PCF::from(Atom {
                    predicate: Pred::from("P"),
                    terms: vec![term!(f(x, y))],
                }),
                PCF::from(Atom {
                    predicate: Pred::from("Q"),
                    terms: vec![term!(f(x, y))],
                }),
            ]);
            assert_eq!(
                "($f(x, y, ?0) ∧ P(?0)) ∨ ($f(x, y, ?1) ∧ Q(?1))",
                clause_set.relational().to_string()
            );
        }
    }

    #[test]
    fn relational_free_vars() {
        {
            let gnf = GNF::try_from(fof!({'|'} -> {_|_})).unwrap();
            let (body, head) = gnf.into_body_and_head();
            let body = body.relational();
            let head = head.relational();
            assert_eq!(Vec::<&Var>::new(), body.free_vars());
            assert_eq!(Vec::<&Var>::new(), head.free_vars());
        }
        {
            // !! make sure the test gnf is not getting simplified by the conversion algorithm.
            let gnf = GNF::try_from(
                fof!({[[P(x)] & [Q(x, y)]] & [P(z)]} -> {[(P(x)) & ([z] = [y])] | [Q(x, y)]}),
            )
            .unwrap();
            let (body, head) = gnf.into_body_and_head();
            let body = body.relational();
            let head = head.relational();
            assert_eq_sorted_vecs!(
                vec![v!(x), v!(y), v!(z)].iter().collect::<Vec<_>>(),
                body.free_vars()
            );
            assert_eq_sorted_vecs!(
                vec![v!(x), v!(y), v!(z)].iter().collect::<Vec<_>>(),
                head.free_vars()
            );
        }
    }

    #[test]
    fn relational_transform() {
        let gnf = GNF::try_from(
            fof!({[[P(x)] & [Q(x, y)]] & [P(z)]} -> {[(P(x)) & ([z] = [y])] | [Q(x, y)]}),
        )
        .unwrap();
        let f = |t: &Variable| {
            {
                if *t == Var::from("x").into() {
                    Var::from("z").into()
                } else {
                    t.clone()
                }
            }
            .into()
        };

        let (body, head) = gnf.into_body_and_head();
        let body = body.relational();
        let head = head.relational();
        assert_eq!(
            fof!([[P(z)] & [P(z)]] & [Q(z, y)]),
            FOF::from(body.transform_term(&f))
        );
        assert_eq!(
            fof!([(P(z)) & ([z] = [y])] | [Q(z, y)]),
            FOF::from(head.transform_term(&f))
        );
    }

    #[test]
    fn relational_signature() {
        {
            let mut sig_body = Sig::new();
            sig_body
                .add_predicate(PredSig {
                    symbol: "P".into(),
                    arity: 1,
                })
                .unwrap();
            sig_body
                .add_predicate(PredSig {
                    symbol: "Q".into(),
                    arity: 2,
                })
                .unwrap();
            let mut sig_head = sig_body.clone();
            sig_head
                .add_predicate(PredSig {
                    symbol: EQ_SYM.into(),
                    arity: 2,
                })
                .unwrap();

            let gnf = GNF::try_from(
                fof!({[[P(x)] & [Q(x, y)]] & [P(z)]} -> {[(P(x)) & ([z] = [y])] | [Q(x, y)]}),
            )
            .unwrap();
            let (body, head) = gnf.into_body_and_head();
            let body = body.relational();
            let head = head.relational();
            assert_eq!(sig_body, body.signature().unwrap());
            assert_eq!(sig_head, head.signature().unwrap());
        }
        {
            let gnf = GNF::try_from(
                fof!({[[P(x)] & [Q(x, y)]] & [P(z, z)]} -> {[(P(x)) & ([z] = [y])] | [P(x, y)]}),
            )
            .unwrap();
            let (body, head) = gnf.into_body_and_head();
            let body = body.relational();
            let head = head.relational();
            assert!(body.signature().is_err());
            assert!(head.signature().is_err());
        }
    }
}
