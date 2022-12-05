/*! Defines formulae in Conjunctive Normal Form (CNF) and implements an algorithm for
transforming an [`SNF`] to a [`CNF`].

[`SNF`]: crate::transform::SNF
 */

use std::ops::Deref;

use super::{ToPNF, ToSNF, PNF, SNF};
use crate::syntax::{
    formula::{
        clause::{Clause, ClauseSet, Literal},
        Exists, Forall, FormulaEx, *,
    },
    term::Complex,
    Error, Sig, Var, FOF,
};
use itertools::Itertools;

// CNF clauses and clause sets are constructed over complex terms.
type CNFClause = Clause<Complex>;

#[derive(Clone)]
pub struct CNFClauseSet(ClauseSet<Complex>);

impl Deref for CNFClauseSet {
    type Target = ClauseSet<Complex>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<ClauseSet<Complex>> for CNFClauseSet {
    fn from(value: ClauseSet<Complex>) -> Self {
        Self(value)
    }
}

impl Default for CNFClauseSet {
    fn default() -> Self {
        ClauseSet::default().into()
    }
}

/// Represents a [`PNF`] with a matrix in Conjunctive Normal Form (CNF).
///
/// **Hint**: A CNF is a firsts-order formula that is a conjunction of zero or
/// more [`Clause`]s where each clause is a disjunction of [`Literal`]s.
#[derive(Clone, Debug)]
pub enum CNF {
    /// Is the quantifier-free portion of a [`PNF`].
    Clauses(ClauseSet<Complex>),

    /// Is an existentially quantified PNF, wrapping an [`Exists`].
    Exists(Box<Exists<CNF>>),

    /// Is a universally quantified PNF, wrapping a [`Forall`].
    Forall(Box<Forall<CNF>>),
}

impl CNF {
    fn clause_to_fof(clause: CNFClause) -> FOF {
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
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
    }
}

impl FormulaEx for CNF {
    fn precedence(&self) -> u8 {
        match self {
            Self::Clauses(_) => PRECEDENCE_AND,
            Self::Exists(this) => this.precedence(),
            Self::Forall(this) => this.precedence(),
        }
    }
}

impl From<ClauseSet<Complex>> for CNF {
    fn from(value: ClauseSet<Complex>) -> Self {
        Self::Clauses(value)
    }
}

impl From<CNFClauseSet> for CNF {
    fn from(value: CNFClauseSet) -> Self {
        value.0.into()
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`CNF`].
pub trait ToCNF: Formula {
    /// Transform `self` to a Conjunctive Normal Form (CNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToCNF;
    ///
    /// let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
    /// let cnf = formula.cnf();
    /// assert_eq!("(P(x) ∨ ¬Q(y)) ∧ (Q(y) ∨ ¬P(x))", cnf.to_string());
    /// ```
    fn cnf(&self) -> CNF;
}

impl ToCNF for PNF {
    fn cnf(&self) -> CNF {
        use super::ToNNF;
        // Compromising type safety to avoid implementing a number of
        // types arising from pairwise combinations of PNF, NNF and NNF:
        let nnf = FOF::from(self.clone()).nnf();
        cnf(distribute_or(&nnf.into()))
    }
}

impl<T: ToPNF> ToCNF for T {
    fn cnf(&self) -> CNF {
        self.pnf().cnf()
    }
}

impl<T: ToCNF> From<T> for CNF {
    fn from(value: T) -> Self {
        value.cnf()
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`CNFClauseSet`].
/// Unlike a [`CNF`], a [`CNFClauseSet`] is quantifier-free; that is, assuming
/// free-variables are universally quantified, the input must be Skolemized (see [`SNF`]).
pub trait ToCNFClauseSet: Formula {
    /// Transform `self` to a Conjunctive Normal Form (CNF) clause set.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToCNFClauseSet;
    ///
    /// let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
    /// let clauses = formula.cnf_clause_set();
    /// assert_eq!("(P(x) ∨ ¬Q(y)) ∧ (Q(y) ∨ ¬P(x))", clauses.to_string());
    /// ```
    fn cnf_clause_set(&self) -> CNFClauseSet;
}

impl ToCNFClauseSet for SNF {
    fn cnf_clause_set(&self) -> CNFClauseSet {
        use super::ToNNF;
        let nnf = FOF::from(self.clone()).nnf();
        cnf_clause_set(distribute_or(&nnf.into()))
    }
}

impl<T: ToSNF> ToCNFClauseSet for T {
    fn cnf_clause_set(&self) -> CNFClauseSet {
        self.snf().cnf_clause_set()
    }
}

impl<T: ToCNFClauseSet> From<T> for CNFClauseSet {
    fn from(value: T) -> Self {
        value.cnf_clause_set()
    }
}

impl std::fmt::Display for CNFClauseSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl std::fmt::Display for CNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl Default for CNF {
    fn default() -> Self {
        Self::from(ClauseSet::<_>::default())
    }
}

impl Formula for CNF {
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

impl From<CNF> for FOF {
    fn from(value: CNF) -> Self {
        match value {
            CNF::Clauses(this) => clause_set_to_fof(this),
            CNF::Exists(this) => FOF::exists(this.variables, this.formula.into()),
            CNF::Forall(this) => FOF::forall(this.variables, this.formula.into()),
        }
    }
}

impl From<&CNF> for FOF {
    fn from(value: &CNF) -> Self {
        value.clone().into()
    }
}

fn clause_set_to_fof(value: ClauseSet<Complex>) -> FOF {
    value
        .into_iter()
        .sorted()
        .into_iter()
        .map(CNF::clause_to_fof)
        .fold1(|item, acc| item.and(acc))
        .unwrap_or(FOF::Top)
}

impl From<CNFClauseSet> for FOF {
    fn from(value: CNFClauseSet) -> Self {
        clause_set_to_fof(value.0)
    }
}

impl From<&CNFClauseSet> for FOF {
    fn from(value: &CNFClauseSet) -> Self {
        value.clone().into()
    }
}

// Distributes conjunctions in the given formula.
// The function assumes that its input is in NNF and SNF.
fn distribute_or(formula: &FOF) -> FOF {
    match formula {
        FOF::Top | FOF::Bottom | FOF::Atom { .. } | FOF::Equals { .. } | FOF::Not { .. } => {
            formula.clone()
        }
        FOF::And(this) => distribute_or(&this.left).and(distribute_or(&this.right)),
        FOF::Or(this) => {
            let left = distribute_or(&this.left);
            let right = distribute_or(&this.right);
            if let FOF::And(left) = left {
                let first = left.left.or(right.clone());
                let second = left.right.or(right);
                distribute_or(&first).and(distribute_or(&second))
            } else if let FOF::And(right) = right {
                let first = left.clone().or(right.left);
                let second = left.or(right.right);
                distribute_or(&first).and(distribute_or(&second))
            } else {
                left.or(right)
            }
        }
        FOF::Forall(this) => FOF::forall(this.variables.clone(), distribute_or(&this.formula)),
        FOF::Exists(this) => FOF::exists(this.variables.clone(), distribute_or(&this.formula)),
        _ => unreachable!(), // `formula` is both in SNF and NNF
    }
}

fn clause_set(formula: FOF) -> ClauseSet<Complex> {
    match formula {
        FOF::Top => ClauseSet::default(),
        FOF::Bottom => ClauseSet::from(Clause::default()),
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
            left.union(&right)
        }
        FOF::Or(this) => {
            let left = clause_set(this.left);
            let right = clause_set(this.right);
            if left.is_empty() {
                left.into()
            } else if right.is_empty() {
                right.into()
            } else if left.len() == 1 && right.len() == 1 {
                let left = left.into_clauses().into_iter().next().unwrap();
                let right = right.into_clauses().into_iter().next().unwrap();
                let clause = left.union(&right);
                ClauseSet::from(clause).into()
            } else {
                unreachable!() // Disjunction is distributed over conjunction in `formula`
            }
        }
        _ => unreachable!(), // `formula` is in PNF
    }
}

fn cnf_clause_set(formula: FOF) -> CNFClauseSet {
    match formula {
        FOF::Forall(this) => cnf_clause_set(this.formula),
        FOF::Exists(this) => cnf_clause_set(this.formula),
        _ => clause_set(formula).into(),
    }
}

fn cnf(formula: FOF) -> CNF {
    match formula {
        FOF::Forall(this) => CNF::Forall(Box::new(Forall {
            variables: this.variables,
            formula: cnf(this.formula),
        })),
        FOF::Exists(this) => CNF::Exists(Box::new(Exists {
            variables: this.variables,
            formula: cnf(this.formula),
        })),
        _ => CNF::Clauses(clause_set(formula)),
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

    fn cnf(formula: &FOF) -> FOF {
        formula.pnf().cnf().into()
    }

    fn cnf_clause_set(formula: &FOF) -> FOF {
        formula.snf().cnf_clause_set().into()
    }

    #[test]
    fn test_cnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_string!("true", cnf(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_string!("false", cnf(&formula));
        }
        {
            let formula: FOF = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", cnf(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", cnf(&formula));
        }
        {
            let formula: FOF = "x=y".parse().unwrap();
            assert_debug_string!("x = y", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("Q(y) | ~P(x)", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("(P(x) | ~Q(y)) & (Q(y) | ~P(x))", cnf(&formula));
        }
        {
            let formula: FOF = "!x. P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("! x. P(f(), g(f(), x))", cnf(&formula));
        }
        // quantifier-free formulae
        {
            let formula: FOF = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x1) | ~Q(y)) & (~P(x2) | ~Q(y))", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) | Q(x)) & (P(x) | ~Q(y))", cnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("(R(z) | ~P(x)) & (R(z) | ~Q(y))", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!(
                        "((((P(x) | Q(x)) | Q(y)) & ((P(x) | Q(x)) | ~Q(x))) & ((P(x) | Q(y)) | ~Q(y))) & ((P(x) | ~Q(x)) | ~Q(y))",
                                        cnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "(((P(x) | Q(y)) | ~R(z)) & (R(z) | ~P(x))) & (R(z) | ~Q(y))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!(
                "((P(x) | Q(x)) | R(y)) & ((P(x) | Q(x)) | R(z))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!(
                "(((P(x1) | Q(x1)) & (P(x1) | Q(x2))) & (P(x2) | Q(x1))) & (P(x2) | Q(x2))",
                cnf(&formula),
            );
        }
        //random formulae
        {
            let formula: FOF = "?x. P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", cnf(&formula));
        }
        {
            let formula: FOF = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("? x. (P(x) & Q(f(), x))", cnf(&formula));
        }
        {
            let formula: FOF = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("! x. (! y. ((R(x) | ~P(y)) | ~Q(x, y)))", cnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("! x. (! y. ((~P(x) | ~Q(y)) | ~R(x, y)))", cnf(&formula));
        }
        {
            let formula: FOF = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "! y. (! x. ((Q(y) | ~P(y, x)) & (Q(y) | ~Q(x))))",
                cnf(&formula)
            );
        }
        {
            let formula: FOF = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "! y. (? x. ((Q(y) | ~P(y, x)) & (Q(y) | ~Q(x))))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x. (? y. P(x, y))", cnf(&formula));
        }
        {
            let formula: FOF = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x, y. P(x, y)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x. (? y. P(x, y))", cnf(&formula));
        }
        {
            let formula: FOF =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
            "? u. (! x, y. (! u`, x`, w. (((P(u, x) | ~R(z)) & (~Q(u`, x`, y) | ~R(z))) & (~R(z) | ~(w = f(u`))))))",
                cnf(&formula)
            );
        }
        {
            let formula: FOF = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "! x. (! y. (? y`. ((P(y) | Q(y`, x)) & (Q(y`, x) | ~Q(x, y)))))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "! x. (? y. (? y`. ((P(y) | Q(y`, x)) & (Q(y`, x) | ~Q(x, y)))))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "? x. (! y, z. (P(x) & ((y = z | ~Q(x, y)) | ~Q(x, z))))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "! x. (! y. (? y`. ((((P(f(x, y)) | ~P(x)) | ~P(y)) & (Q(x, y`) | ~P(x))) & (~P(x) | ~P(y`)))))",
                cnf(&formula));
        }
    }

    #[test]
    fn test_cnf_clause_set() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_string!("true", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_string!("false", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "x=y".parse().unwrap();
            assert_debug_string!("x = y", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("Q(y) | ~P(x)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("(P(x) | ~Q(y)) & (Q(y) | ~P(x))", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", cnf_clause_set(&formula));
        }
        // quantifier-free formulae
        {
            let formula: FOF = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!(
                "(~P(x1) | ~Q(y)) & (~P(x2) | ~Q(y))",
                cnf_clause_set(&formula)
            );
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) | Q(x)) & (P(x) | ~Q(y))", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("(R(z) | ~P(x)) & (R(z) | ~Q(y))", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!(
                        "((((P(x) | Q(x)) | Q(y)) & ((P(x) | Q(x)) | ~Q(x))) & ((P(x) | Q(y)) | ~Q(y))) & ((P(x) | ~Q(x)) | ~Q(y))",
                                        cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "(((P(x) | Q(y)) | ~R(z)) & (R(z) | ~P(x))) & (R(z) | ~Q(y))",
                cnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!(
                "((P(x) | Q(x)) | R(y)) & ((P(x) | Q(x)) | R(z))",
                cnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!(
                "(((P(x1) | Q(x1)) & (P(x1) | Q(x2))) & (P(x2) | Q(x1))) & (P(x2) | Q(x2))",
                cnf_clause_set(&formula),
            );
        }
        //random formulae
        {
            let formula: FOF = "?x. P(x)".parse().unwrap();
            assert_debug_string!("P('c#0)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('c#0) & Q(f(), 'c#0)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("(R(x) | ~P(y)) | ~Q(x, y)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x) | ~Q(y)) | ~R(x, y)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "(Q(y) | ~P(y, x)) & (Q(y) | ~Q(x))",
                cnf_clause_set(&formula)
            );
        }
        {
            let formula: FOF = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "(Q(y) | ~P(y, f#0(y))) & (Q(y) | ~Q(f#0(y)))",
                cnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", cnf_clause_set(&formula));
        }
        {
            let formula: FOF = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, f#0(x))", cnf_clause_set(&formula));
        }
        {
            let formula: FOF =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
                "((P(f#0(z), x) | ~R(z)) & (~Q(u`, x`, y) | ~R(z))) & (~R(z) | ~(w = f(u`)))",
                cnf_clause_set(&formula)
            );
        }
        {
            let formula: FOF = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(y) | Q(f#0(x, y), x)) & (Q(f#0(x, y), x) | ~Q(x, y))",
                cnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(f#0(x)) | Q(f#1(x), x)) & (Q(f#1(x), x) | ~Q(x, f#0(x)))",
                cnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "P('c#0) & ((y = z | ~Q('c#0, y)) | ~Q('c#0, z))",
                cnf_clause_set(&formula),
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(((P(f(x, y)) | ~P(x)) | ~P(y)) & (Q(x, f#0(x, y)) | ~P(x))) & (~P(x) | ~P(f#0(x, y)))",
                cnf_clause_set(&formula));
        }
    }

    #[test]
    fn cnf_free_vars() {
        {
            let cnf = fof!('|').cnf();
            assert_eq!(Vec::<&Var>::new(), cnf.free_vars());
        }
        {
            let cnf = fof!({P(x, @c)} & {[Q(x)] & [ [Q(y)] | [R()] ]}).cnf();
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), cnf.free_vars());
        }
    }

    #[test]
    fn cnf_transform() {
        let cnf = fof!({ P(y, f(x)) } & { [Q(f(x))] & [[R(f(x))] | [R(y)]] }).cnf();
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
            fof!({ [P(y, z)] & [Q(z)] } & { [R(y)] | [R(z)] }),
            FOF::from(cnf.transform_term(&f))
        );
    }

    #[test]
    fn cnf_signature() {
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

            let cnf = fof!({P(f(x, @c))} & {[P(y)] & [[Q(x, x)] | [(x) = (y)]]}).cnf();
            assert_eq!(sig, cnf.signature().unwrap());
        }
        {
            let cnf = fof!({ P(x, x) } & { P(x) }).cnf();
            assert!(cnf.signature().is_err());
        }
    }
}
