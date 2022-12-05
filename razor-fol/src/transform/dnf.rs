/*! Defines formulae in Disjunctive Normal Form (DNF) and implements an algorithm for
transforming an [`SNF`] to a [`DNF`].

[`SNF`]: crate::transform::SNF
 */

use std::ops::Deref;

use super::{ToPNF, ToSNF, PNF, SNF};
use crate::syntax::{
    formula::{
        clause::{Clause, ClauseSet, Literal},
        Exists, Forall, *,
    },
    term::Complex,
    Error, Sig, Var, FOF,
};
use itertools::Itertools;

// DNF clauses and clause sets are constructed over complex terms.
type DNFClause = Clause<Complex>;
#[derive(Clone)]
pub struct DNFClauseSet(ClauseSet<Complex>);

impl From<ClauseSet<Complex>> for DNFClauseSet {
    fn from(value: ClauseSet<Complex>) -> Self {
        Self(value)
    }
}

impl Deref for DNFClauseSet {
    type Target = ClauseSet<Complex>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Represents a [`PNF`] with a matrix in Disjunctive Normal Form (DNF).
///
/// **Hint**: A DNF is a firsts-order formula that is a disjunction of zero or
/// more [`Clause`]s where each clause is a conjunction of [`Literal`]s.
#[derive(Clone)]
pub enum DNF {
    /// Is the quantifier-free portion of a [`PNF`].
    Clauses(ClauseSet<Complex>),

    /// Is an existentially quantified PNF, wrapping an [`Exists`].
    Exists(Box<Exists<DNF>>),

    /// Is a universally quantified PNF, wrapping a [`Forall`].
    Forall(Box<Forall<DNF>>),
}

impl DNF {
    fn clause_to_fof(clause: DNFClause) -> FOF {
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
                    Atomic::Atom(this) => FOF::not(this.into()),
                    Atomic::Equals(this) => FOF::not(this.into()),
                },
            })
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

impl FormulaEx for DNF {
    fn precedence(&self) -> u8 {
        match self {
            DNF::Clauses(_) => PRECEDENCE_OR,
            DNF::Exists(this) => this.precedence(),
            DNF::Forall(this) => this.precedence(),
        }
    }
}

impl From<ClauseSet<Complex>> for DNF {
    fn from(value: ClauseSet<Complex>) -> Self {
        Self::Clauses(value)
    }
}

impl From<DNFClauseSet> for DNF {
    fn from(value: DNFClauseSet) -> Self {
        value.0.into()
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`DNF`].
pub trait ToDNF: Formula {
    /// Transform `self` to a Disjunctive Normal Form (DNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToDNF;
    ///
    /// let formula: FOF = "P(x) iff Q(y)".parse().unwrap();
    /// let dnf = formula.dnf();
    ///
    /// assert_eq!(
    ///    "(((P(x) ∧ Q(y)) ∨ (P(x) ∧ ¬P(x))) ∨ (Q(y) ∧ ¬Q(y))) ∨ (¬P(x) ∧ ¬Q(y))",
    ///    dnf.to_string()
    /// );
    /// ```    
    fn dnf(&self) -> DNF;
}

impl ToDNF for PNF {
    fn dnf(&self) -> DNF {
        use super::ToNNF;

        // Compromising type safety to avoid implementing a number of
        // types arising from pairwise combinations of PNF, SNF and NNF:
        let nnf = FOF::from(self.clone()).nnf();
        dnf(distribute_and(&nnf.into()))
    }
}

impl<T: ToPNF> ToDNF for T {
    fn dnf(&self) -> DNF {
        self.pnf().dnf()
    }
}

impl<T: ToDNF> From<T> for DNF {
    fn from(value: T) -> Self {
        value.dnf()
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`DNFClauseSet`].
/// Unlike a [`DNF`], a [`DNFClauseSet`] is quantifier-free; that is, assuming
/// free-variables are universally quantified, the input must be Skolemized (see [`SNF`]).
pub trait ToDNFClauseSet: Formula {
    /// Transform `self` to a Conjunctive Normal Form (DNF) clause set.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToDNFClauseSet;
    ///
    /// let formula: FOF = "P(x) iff Q(y)".parse().unwrap();
    /// let clauses = formula.dnf_clause_set();
    ///
    /// assert_eq!(
    ///    "(((P(x) ∧ Q(y)) ∨ (P(x) ∧ ¬P(x))) ∨ (Q(y) ∧ ¬Q(y))) ∨ (¬P(x) ∧ ¬Q(y))",
    ///    clauses.to_string()
    /// );
    /// ```
    fn dnf_clause_set(&self) -> DNFClauseSet;
}

impl ToDNFClauseSet for SNF {
    fn dnf_clause_set(&self) -> DNFClauseSet {
        use super::ToNNF;
        let nnf = FOF::from(self.clone()).nnf();
        dnf_clause_set(distribute_and(&nnf.into()))
    }
}

impl<T: ToSNF> ToDNFClauseSet for T {
    fn dnf_clause_set(&self) -> DNFClauseSet {
        self.snf().dnf_clause_set()
    }
}

impl<T: ToDNFClauseSet> From<T> for DNFClauseSet {
    fn from(value: T) -> Self {
        value.dnf_clause_set()
    }
}

impl std::fmt::Display for DNFClauseSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl std::fmt::Display for DNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl Default for DNF {
    fn default() -> Self {
        Self::Clauses(ClauseSet::<_>::default().into())
    }
}

impl Formula for DNF {
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

impl From<DNF> for FOF {
    fn from(value: DNF) -> Self {
        match value {
            DNF::Clauses(this) => clause_set_to_fof(this),
            DNF::Exists(this) => FOF::exists(this.variables, this.formula.into()),
            DNF::Forall(this) => FOF::forall(this.variables, this.formula.into()),
        }
    }
}

impl From<&DNF> for FOF {
    fn from(value: &DNF) -> Self {
        value.clone().into()
    }
}

fn clause_set_to_fof(value: ClauseSet<Complex>) -> FOF {
    value
        .into_iter()
        .sorted()
        .into_iter()
        .map(DNF::clause_to_fof)
        .fold1(|item, acc| item.or(acc))
        .unwrap_or(FOF::Bottom)
}

impl From<DNFClauseSet> for FOF {
    fn from(value: DNFClauseSet) -> Self {
        clause_set_to_fof(value.0)
    }
}

impl From<&DNFClauseSet> for FOF {
    fn from(value: &DNFClauseSet) -> Self {
        value.clone().into()
    }
}

// Distributes disjunction in the given formula. The function assumes that its input is an NNF.
fn distribute_and(formula: &FOF) -> FOF {
    match formula {
        FOF::Top | FOF::Bottom | FOF::Atom { .. } | FOF::Equals { .. } | FOF::Not { .. } => {
            formula.clone()
        }
        FOF::Or(this) => distribute_and(&this.left).or(distribute_and(&this.right)),
        FOF::And(this) => {
            let left = distribute_and(&this.left);
            let right = distribute_and(&this.right);
            if let FOF::Or(left) = left {
                let first = left.left.and(right.clone());
                let second = left.right.and(right);
                distribute_and(&first).or(distribute_and(&second))
            } else if let FOF::Or(right) = right {
                distribute_and(&left.clone().and(right.left))
                    .or(distribute_and(&left.and(right.right)))
            } else {
                left.and(right)
            }
        }
        FOF::Forall(this) => FOF::forall(this.variables.clone(), distribute_and(&this.formula)),
        FOF::Exists(this) => FOF::exists(this.variables.clone(), distribute_and(&this.formula)),
        _ => unreachable!(), // `formula` is both in SNF and NNF
    }
}

fn clause_set(formula: FOF) -> ClauseSet<Complex> {
    match formula {
        FOF::Top => ClauseSet::from(Clause::default()),
        FOF::Bottom => ClauseSet::default(),
        FOF::Atom(this) => {
            let clause = Clause::from(Literal::from(this));
            ClauseSet::from(clause)
        }
        FOF::Equals(this) => {
            let clause = Clause::from(Literal::from(this));
            ClauseSet::from(clause)
        }
        FOF::Not(this) => match this.formula {
            FOF::Atom(atom) => {
                let lit: Literal<_> = Not { formula: atom }.into();
                let clause = Clause::from(lit);
                ClauseSet::from(clause)
            }
            FOF::Equals(eq) => {
                let lit: Literal<_> = Not { formula: eq }.into();
                let clause = Clause::from(lit);
                ClauseSet::from(clause)
            }
            _ => unreachable!(), // `formula` is in NNF
        },
        FOF::And(this) => {
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
        FOF::Or(this) => {
            let left = clause_set(this.left);
            let right = clause_set(this.right);
            left.union(&right)
        }
        _ => unreachable!(), // `formula` is in SNF
    }
}

fn dnf_clause_set(formula: FOF) -> DNFClauseSet {
    match formula {
        FOF::Exists(this) => dnf_clause_set(this.formula),
        FOF::Forall(this) => dnf_clause_set(this.formula),
        _ => clause_set(formula).into(),
    }
}

fn dnf(formula: FOF) -> DNF {
    match formula {
        FOF::Forall(this) => DNF::Forall(Box::new(Forall {
            variables: this.variables,
            formula: dnf(this.formula),
        })),
        FOF::Exists(this) => DNF::Exists(Box::new(Exists {
            variables: this.variables,
            formula: dnf(this.formula),
        })),
        _ => DNF::Clauses(clause_set(formula)),
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

    fn dnf_clause_set(formula: &FOF) -> FOF {
        formula.snf().dnf_clause_set().into()
    }

    #[test]
    fn test_dnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_string!("true", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_string!("false", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "x=y".parse().unwrap();
            assert_debug_string!("x = y", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("Q(y) | ~P(x)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "(((P(x) & Q(y)) | (P(x) & ~P(x))) | (Q(y) & ~Q(y))) | (~P(x) & ~Q(y))",
                dnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", dnf_clause_set(&formula));
        }
        // quantifier-free formulae
        {
            let formula: FOF = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x1) & ~P(x2)) | ~Q(y)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | (Q(x) & ~Q(y))", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("R(z) | (~P(x) & ~Q(y))", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!(
                "(P(x) | (Q(x) & ~Q(y))) | (Q(y) & ~Q(x))",
                dnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!("(((((P(x) & R(z)) | ((P(x) & ~P(x)) & ~Q(y))) | (Q(y) & R(z))) | ((Q(y) & ~P(x)) & ~Q(y))) | (R(z) & ~R(z))) | ((~P(x) & ~Q(y)) & ~R(z))",
                                dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!("(P(x) | Q(x)) | (R(y) & R(z))", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!(
                "(P(x1) & P(x2)) | (Q(x1) & Q(x2))",
                dnf_clause_set(&formula)
            );
        }

        //random formulae
        {
            let formula: FOF = "?x. P(x)".parse().unwrap();
            assert_debug_string!("P('c#0)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('c#0) & Q(f(), 'c#0)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("(R(x) | ~P(y)) | ~Q(x, y)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x) | ~Q(y)) | ~R(x, y)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("Q(y) | (~P(y, x) & ~Q(x))", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "Q(y) | (~P(y, f#0(y)) & ~Q(f#0(y)))",
                dnf_clause_set(&formula)
            );
        }
        {
            let formula: FOF = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", dnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, f#0(x))", dnf_clause_set(&formula));
        }
        {
            let formula: FOF =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
                "((P(f#0(z), x) & ~Q(u`, x`, y)) & ~(w = f(u`))) | ~R(z)",
                dnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(y) & ~Q(x, y)) | Q(f#0(x, y), x)",
                dnf_clause_set(&formula)
            );
        }
        {
            let formula: FOF = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(f#0(x)) & ~Q(x, f#0(x))) | Q(f#1(x), x)",
                dnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "((P(\'c#0) & y = z) | (P(\'c#0) & ~Q(\'c#0, y))) | (P(\'c#0) & ~Q(\'c#0, z))",
                dnf_clause_set(&formula)
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
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
            FOF::from(dnf.transform_term(&f))
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
