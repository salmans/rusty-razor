/*! Defines formulae in Disjunctive Normal Form (DNF) and implements an algorithm for
transforming a [`Pnf`] to a [`Dnf`].

[`Pnf`]: crate::transform::Pnf
 */

use std::ops::Deref;

use super::{Pnf, Snf, ToPnf, ToSnf};
use crate::syntax::{
    formula::{
        clause::{Clause, ClauseSet, Literal},
        Exists, Forall, *,
    },
    term::Complex,
    Error, Fof, Sig, Var,
};
use itertools::Itertools;

// DNF clauses and clause sets are constructed over complex terms.
type DnfClause = Clause<Complex>;
#[derive(Clone)]
pub struct DnfClauseSet(ClauseSet<Complex>);

impl From<ClauseSet<Complex>> for DnfClauseSet {
    fn from(value: ClauseSet<Complex>) -> Self {
        Self(value)
    }
}

impl Deref for DnfClauseSet {
    type Target = ClauseSet<Complex>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Represents a [`Pnf`] with a matrix in Disjunctive Normal Form (DNF).
///
/// **Hint**: A DNF is a firsts-order formula that is a disjunction of zero or
/// more [`Clause`]s where each clause is a conjunction of [`Literal`]s.
#[derive(Clone)]
pub enum Dnf {
    /// Is the quantifier-free portion of a [`Pnf`].
    Clauses(ClauseSet<Complex>),

    /// Is an existentially quantified PNF, wrapping an [`Exists`].
    Exists(Box<Exists<Dnf>>),

    /// Is a universally quantified PNF, wrapping a [`Forall`].
    Forall(Box<Forall<Dnf>>),
}

impl Dnf {
    fn clause_to_fof(clause: DnfClause) -> Fof {
        clause
            .into_literals()
            .into_iter()
            .sorted()
            .into_iter()
            .map(|clause| match clause {
                Literal::Pos(pos) => match pos {
                    Atomic::Atom(this) => this.into(),
                    Atomic::Equals(this) => this.into(),
                },
                Literal::Neg(neg) => match neg {
                    Atomic::Atom(this) => Fof::not(this.into()),
                    Atomic::Equals(this) => Fof::not(this.into()),
                },
            })
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(Fof::Top)
    }
}

impl FormulaEx for Dnf {
    fn precedence(&self) -> u8 {
        match self {
            Dnf::Clauses(_) => PRECEDENCE_OR,
            Dnf::Exists(this) => this.precedence(),
            Dnf::Forall(this) => this.precedence(),
        }
    }
}

impl From<ClauseSet<Complex>> for Dnf {
    fn from(value: ClauseSet<Complex>) -> Self {
        Self::Clauses(value)
    }
}

impl From<DnfClauseSet> for Dnf {
    fn from(value: DnfClauseSet) -> Self {
        value.0.into()
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`Dnf`].
pub trait ToDnf: Formula {
    /// Transform `self` to a Disjunctive Normal Form (DNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Fof;
    /// use razor_fol::transform::ToDnf;
    ///
    /// let formula: Fof = "P(x) iff Q(y)".parse().unwrap();
    /// let dnf = formula.dnf();
    ///
    /// assert_eq!(
    ///    "(((P(x) ∧ Q(y)) ∨ (P(x) ∧ ¬P(x))) ∨ (Q(y) ∧ ¬Q(y))) ∨ (¬P(x) ∧ ¬Q(y))",
    ///    dnf.to_string()
    /// );
    /// ```    
    fn dnf(&self) -> Dnf;
}

impl ToDnf for Pnf {
    fn dnf(&self) -> Dnf {
        use super::ToNnf;

        // Compromising type safety to avoid implementing a number of
        // types arising from pairwise combinations of PNF, SNF and NNF:
        let nnf = Fof::from(self.clone()).nnf();
        dnf(distribute_and(&nnf.into()))
    }
}

impl<T: ToPnf> ToDnf for T {
    fn dnf(&self) -> Dnf {
        self.pnf().dnf()
    }
}

impl<T: ToDnf> From<T> for Dnf {
    fn from(value: T) -> Self {
        value.dnf()
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`DnfClauseSet`].
/// Unlike a [`Dnf`], a [`DnfClauseSet`] is quantifier-free; that is, assuming
/// free-variables are universally quantified, the input must be Skolemized (see [`Snf`]).
pub trait ToDnfClauseSet: Formula {
    /// Transform `self` to a Conjunctive Normal Form (DNF) clause set.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Fof;
    /// use razor_fol::transform::ToDnfClauseSet;
    ///
    /// let formula: Fof = "P(x) iff Q(y)".parse().unwrap();
    /// let clauses = formula.dnf_clause_set();
    ///
    /// assert_eq!(
    ///    "(((P(x) ∧ Q(y)) ∨ (P(x) ∧ ¬P(x))) ∨ (Q(y) ∧ ¬Q(y))) ∨ (¬P(x) ∧ ¬Q(y))",
    ///    clauses.to_string()
    /// );
    /// ```
    fn dnf_clause_set(&self) -> DnfClauseSet;
}

impl ToDnfClauseSet for Snf {
    fn dnf_clause_set(&self) -> DnfClauseSet {
        use super::ToNnf;
        let nnf = Fof::from(self.clone()).nnf();
        dnf_clause_set(distribute_and(&nnf.into()))
    }
}

impl<T: ToSnf> ToDnfClauseSet for T {
    fn dnf_clause_set(&self) -> DnfClauseSet {
        self.snf().dnf_clause_set()
    }
}

impl<T: ToDnfClauseSet> From<T> for DnfClauseSet {
    fn from(value: T) -> Self {
        value.dnf_clause_set()
    }
}

impl std::fmt::Display for DnfClauseSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Fof::from(self).fmt(f)
    }
}

impl std::fmt::Display for Dnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Fof::from(self).fmt(f)
    }
}

impl Default for Dnf {
    fn default() -> Self {
        Self::Clauses(ClauseSet::<_>::default())
    }
}

impl Formula for Dnf {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        match self {
            Self::Clauses(this) => this.signature(),
            Self::Exists(this) => this.signature(),
            Self::Forall(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&Var> {
        match self {
            Self::Clauses(this) => this.free_vars(),
            Self::Exists(this) => this.free_vars(),
            Self::Forall(this) => this.free_vars(),
        }
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            Self::Clauses(this) => this.transform_term(f).into(),
            Self::Exists(this) => Self::Exists(Box::new(this.transform_term(f))),
            Self::Forall(this) => Self::Forall(Box::new(this.transform_term(f))),
        }
    }
}

impl From<Dnf> for Fof {
    fn from(value: Dnf) -> Self {
        match value {
            Dnf::Clauses(this) => clause_set_to_fof(this),
            Dnf::Exists(this) => Fof::exists(this.variables, this.formula.into()),
            Dnf::Forall(this) => Fof::forall(this.variables, this.formula.into()),
        }
    }
}

impl From<&Dnf> for Fof {
    fn from(value: &Dnf) -> Self {
        value.clone().into()
    }
}

fn clause_set_to_fof(value: ClauseSet<Complex>) -> Fof {
    value
        .into_iter()
        .sorted()
        .into_iter()
        .map(Dnf::clause_to_fof)
        .fold1(|item, acc| item.or(acc))
        .unwrap_or(Fof::Bottom)
}

impl From<DnfClauseSet> for Fof {
    fn from(value: DnfClauseSet) -> Self {
        clause_set_to_fof(value.0)
    }
}

impl From<&DnfClauseSet> for Fof {
    fn from(value: &DnfClauseSet) -> Self {
        value.clone().into()
    }
}

// Distributes disjunction in the given formula. The function assumes that its input is an NNF.
fn distribute_and(formula: &Fof) -> Fof {
    match formula {
        Fof::Top | Fof::Bottom | Fof::Atom { .. } | Fof::Equals { .. } | Fof::Not { .. } => {
            formula.clone()
        }
        Fof::Or(this) => distribute_and(&this.left).or(distribute_and(&this.right)),
        Fof::And(this) => {
            let left = distribute_and(&this.left);
            let right = distribute_and(&this.right);
            if let Fof::Or(left) = left {
                let first = left.left.and(right.clone());
                let second = left.right.and(right);
                distribute_and(&first).or(distribute_and(&second))
            } else if let Fof::Or(right) = right {
                distribute_and(&left.clone().and(right.left))
                    .or(distribute_and(&left.and(right.right)))
            } else {
                left.and(right)
            }
        }
        Fof::Forall(this) => Fof::forall(this.variables.clone(), distribute_and(&this.formula)),
        Fof::Exists(this) => Fof::exists(this.variables.clone(), distribute_and(&this.formula)),
        _ => unreachable!(), // `formula` is both in SNF and NNF
    }
}

fn clause_set(formula: Fof) -> ClauseSet<Complex> {
    match formula {
        Fof::Top => ClauseSet::from(Clause::default()),
        Fof::Bottom => ClauseSet::default(),
        Fof::Atom(this) => {
            let clause = Clause::from(Literal::from(this));
            ClauseSet::from(clause)
        }
        Fof::Equals(this) => {
            let clause = Clause::from(Literal::from(this));
            ClauseSet::from(clause)
        }
        Fof::Not(this) => match this.formula {
            Fof::Atom(atom) => {
                let lit: Literal<_> = Not { formula: atom }.into();
                let clause = Clause::from(lit);
                ClauseSet::from(clause)
            }
            Fof::Equals(eq) => {
                let lit: Literal<_> = Not { formula: eq }.into();
                let clause = Clause::from(lit);
                ClauseSet::from(clause)
            }
            _ => unreachable!(), // `formula` is in NNF
        },
        Fof::And(this) => {
            let left = clause_set(this.left);
            let right = clause_set(this.right);
            if left.is_empty() {
                left
            } else if right.is_empty() {
                right
            } else if left.len() == 1 && right.len() == 1 {
                let left = left.into_clauses().into_iter().next().unwrap();
                let right = right.into_clauses().into_iter().next().unwrap();
                let clause = left.union(&right);
                ClauseSet::from(clause)
            } else {
                unreachable!() // Conjunction is distributed over disjunction in `formula`
            }
        }
        Fof::Or(this) => {
            let left = clause_set(this.left);
            let right = clause_set(this.right);
            left.union(&right)
        }
        _ => unreachable!(), // `formula` is in SNF
    }
}

fn dnf_clause_set(formula: Fof) -> DnfClauseSet {
    match formula {
        Fof::Exists(this) => dnf_clause_set(this.formula),
        Fof::Forall(this) => dnf_clause_set(this.formula),
        _ => clause_set(formula).into(),
    }
}

fn dnf(formula: Fof) -> Dnf {
    match formula {
        Fof::Forall(this) => Dnf::Forall(Box::new(Forall {
            variables: this.variables,
            formula: dnf(this.formula),
        })),
        Fof::Exists(this) => Dnf::Exists(Box::new(Exists {
            variables: this.variables,
            formula: dnf(this.formula),
        })),
        _ => Dnf::Clauses(clause_set(formula)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assert_debug_string, assert_eq_sorted_vecs, fof,
        syntax::{
            signature::{FuncSig, PredSig},
            EQ_SYM,
        },
        term, v,
    };

    fn dnf_clause_set(formula: &Fof) -> Fof {
        formula.snf().dnf_clause_set().into()
    }

    #[test]
    fn test_dnf() {
        {
            let formula: Fof = "true".parse().unwrap();
            assert_debug_string!("true", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "false".parse().unwrap();
            assert_debug_string!("false", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "x=y".parse().unwrap();
            assert_debug_string!("x = y", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("Q(y) | ~P(x)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "(((P(x) & Q(y)) | (P(x) & ~P(x))) | (Q(y) & ~Q(y))) | (~P(x) & ~Q(y))",
                dnf_clause_set(&formula),
            );
        }
        {
            let formula: Fof = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", dnf_clause_set(&formula));
        }
        // quantifier-free formulae
        {
            let formula: Fof = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x1) & ~P(x2)) | ~Q(y)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | (Q(x) & ~Q(y))", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("R(z) | (~P(x) & ~Q(y))", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!(
                "(P(x) | (Q(x) & ~Q(y))) | (Q(y) & ~Q(x))",
                dnf_clause_set(&formula),
            );
        }
        {
            let formula: Fof = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!("(((((P(x) & R(z)) | ((P(x) & ~P(x)) & ~Q(y))) | (Q(y) & R(z))) | ((Q(y) & ~P(x)) & ~Q(y))) | (R(z) & ~R(z))) | ((~P(x) & ~Q(y)) & ~R(z))",
                                dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!("(P(x) | Q(x)) | (R(y) & R(z))", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!(
                "(P(x1) & P(x2)) | (Q(x1) & Q(x2))",
                dnf_clause_set(&formula)
            );
        }

        //random formulae
        {
            let formula: Fof = "?x. P(x)".parse().unwrap();
            assert_debug_string!("P('c#0)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('c#0) & Q(f(), 'c#0)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("(R(x) | ~P(y)) | ~Q(x, y)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x) | ~Q(y)) | ~R(x, y)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("Q(y) | (~P(y, x) & ~Q(x))", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "Q(y) | (~P(y, f#0(y)) & ~Q(f#0(y)))",
                dnf_clause_set(&formula)
            );
        }
        {
            let formula: Fof = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", dnf_clause_set(&formula));
        }
        {
            let formula: Fof = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, f#0(x))", dnf_clause_set(&formula));
        }
        {
            let formula: Fof =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
                "((P(f#0(z), x) & ~Q(u`, x`, y)) & ~(w = f(u`))) | ~R(z)",
                dnf_clause_set(&formula),
            );
        }
        {
            let formula: Fof = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(y) & ~Q(x, y)) | Q(f#0(x, y), x)",
                dnf_clause_set(&formula)
            );
        }
        {
            let formula: Fof = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(f#0(x)) & ~Q(x, f#0(x))) | Q(f#1(x), x)",
                dnf_clause_set(&formula),
            );
        }
        {
            let formula: Fof = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "((P(\'c#0) & y = z) | (P(\'c#0) & ~Q(\'c#0, y))) | (P(\'c#0) & ~Q(\'c#0, z))",
                dnf_clause_set(&formula)
            );
        }
        {
            let formula: Fof = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                .parse()
                .unwrap();
            assert_debug_string!("(((P(f(x, y)) & Q(x, f#0(x, y))) & ~P(f#0(x, y))) | ((Q(x, f#0(x, y)) & ~P(y)) & ~P(f#0(x, y)))) | ~P(x)", dnf_clause_set(&formula));
        }
    }

    #[test]
    fn dnf_free_vars() {
        {
            let dnf = fof!('|').dnf();
            assert_eq!(Vec::<&Var>::new(), dnf.free_vars());
        }
        {
            let dnf = fof!({P(x, @c)} | {[Q(x)] | [ [Q(y)] & [R()] ]}).dnf();
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), dnf.free_vars());
        }
    }

    #[test]
    fn dnf_transform() {
        let dnf = fof!({ P(y, f(x)) } | { [Q(f(x))] | [[R(f(x))] & [R(y)]] }).dnf();
        let f = |t: &Complex| {
            {
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
            }
            .into()
        };
        assert_eq!(
            fof!({ [P(y, z)] | [Q(z)] } | { [R(y)] & [R(z)] }),
            Fof::from(dnf.transform_term(&f))
        );
    }

    #[test]
    fn dnf_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: "P".into(),
                arity: 1,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: "Q".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: EQ_SYM.into(),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: "f".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_constant("c".into());

            let dnf = fof!({P(f(x, @c))} | {[P(y)] | [[Q(x, x)] & [(x) = (y)]]}).dnf();
            assert_eq!(sig, dnf.signature().unwrap());
        }
        {
            let dnf = fof!({ P(x, x) } | { P(x) }).dnf();
            assert!(dnf.signature().is_err());
        }
    }
}
