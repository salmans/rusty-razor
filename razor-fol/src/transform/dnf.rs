/*! Defines formulae in Disjunctive Normal Form (DNF) and implements an algorithm for
converting [`SNF`] to [`DNF`].

[`SNF`]: crate::transform::SNF
 */

use super::{TermBased, SNF};
use crate::syntax::{formula::*, Error, Sig, Term, FOF, V};
use itertools::Itertools;
use std::ops::Deref;

/// Is a [`DNF`] clause, representing conjunction of zero or more [`Literal`]s.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Clause(Vec<Literal>);

impl Clause {
    /// Consumes the receiver clause and `other` and returns a clause containing
    /// all literals in the receiver and `other`.
    pub fn union(self, other: Self) -> Self {
        let mut lits = self.0;
        lits.extend(other.0);
        lits.into()
    }

    /// Returns the literals of the receiver clause.
    pub fn literals(&self) -> &[Literal] {
        &self.0
    }
}

impl Deref for Clause {
    type Target = [Literal];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Literal> for Clause {
    fn from(value: Literal) -> Self {
        Clause(vec![value])
    }
}

impl<I: IntoIterator<Item = Literal>> From<I> for Clause {
    fn from(value: I) -> Self {
        Clause(value.into_iter().collect())
    }
}

impl Default for Clause {
    fn default() -> Self {
        Clause::from(Vec::<Literal>::new())
    }
}

impl TermBased for Clause {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = Vec::new();
        for lit in &self.0 {
            vs.extend(lit.free_vars());
        }
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Clause(self.0.iter().map(|lit| lit.transform(f)).collect())
    }
}

impl Formula for Clause {
    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|l| l.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }
}

impl From<Clause> for FOF {
    fn from(value: Clause) -> Self {
        value
            .0
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

/// Represents a formula in Disjunctive Normal Form (DNF).
///
/// **Hint**: A DNF is a firsts-order formula that is a disjunction of zero or
/// more [`Clause`]s.
#[derive(Clone)]
pub struct DNF(Vec<Clause>);

impl From<Clause> for DNF {
    fn from(value: Clause) -> Self {
        DNF(vec![value])
    }
}

impl DNF {
    /// Consumes the receiver DNF and `other` and returns a DNF containing
    /// all clauses in the receiver and `other`.    
    pub fn union(self, other: Self) -> Self {
        let mut lits = self.0;
        lits.extend(other.0);
        lits.into()
    }

    /// Returns the clauses of the receiver DNF.
    pub fn clauses(&self) -> &[Clause] {
        &self.0
    }
}

impl Deref for DNF {
    type Target = [Clause];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<I: IntoIterator<Item = Clause>> From<I> for DNF {
    fn from(value: I) -> Self {
        DNF(value.into_iter().collect())
    }
}

impl Default for DNF {
    fn default() -> Self {
        DNF::from(Vec::<Clause>::new())
    }
}

impl From<&SNF> for DNF {
    fn from(value: &SNF) -> Self {
        // Compromising type safety to avoid implementing a number of
        // types arising from pairwise combinations of PNF, SNF and NNF:
        let nnf = FOF::from(value.clone()).nnf();
        dnf(distribute_and(&nnf.into()))
    }
}

impl Formula for DNF {
    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }
}

impl TermBased for DNF {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = Vec::new();
        for clause in &self.0 {
            vs.extend(clause.free_vars());
        }
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        DNF(self.0.iter().map(|clause| clause.transform(f)).collect())
    }
}

impl From<DNF> for FOF {
    fn from(value: DNF) -> Self {
        value
            .0
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
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
        _ => unreachable!(), // NNF input
    }
}

// Eliminates the existential quantifiers of the input formula.
fn dnf(formula: FOF) -> DNF {
    match formula {
        FOF::Top => DNF::from(Clause::default()),
        FOF::Bottom => DNF::default(),
        FOF::Atom(this) => Clause::from(Literal::from(this)).into(),
        FOF::Equals(this) => Clause::from(Literal::from(this)).into(),
        FOF::Not(this) => match this.formula {
            FOF::Atom(atom) => {
                let lit: Literal = Not { formula: atom }.into();
                Clause::from(lit).into()
            }
            FOF::Equals(eq) => {
                let lit: Literal = Not { formula: eq }.into();
                Clause::from(lit).into()
            }
            _ => unreachable!(), // `formula` is in NNF
        },
        FOF::And(this) => {
            let mut left = dnf(this.left);
            let mut right = dnf(this.right);
            if left.0.is_empty() {
                left
            } else if right.0.is_empty() {
                right
            } else if left.0.len() == 1 && right.0.len() == 1 {
                let left = left.0.remove(0);
                let right = right.0.remove(0);
                left.union(right).into()
            } else {
                unreachable!() // Conjunction is distributed over disjunction in `formula`
            }
        }
        FOF::Or(this) => dnf(this.left).union(dnf(this.right)),
        FOF::Forall(this) => dnf(this.formula),
        _ => unreachable!(), // `formula` is in SNF
    }
}

impl SNF {
    /// Transform the receiver SNF to a Disjunctive Normal Form (DNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "P(x) iff Q(y)".parse().unwrap();
    /// let snf = formula.pnf().snf();
    /// let dnf = snf.dnf();
    ///
    /// assert_eq!(
    ///    "((((¬P(x)) ∧ (¬Q(y))) ∨ ((¬P(x)) ∧ P(x))) ∨ (Q(y) ∧ (¬Q(y)))) ∨ (Q(y) ∧ P(x))",
    ///    FOF::from(dnf).to_string()
    /// );
    /// ```
    pub fn dnf(&self) -> DNF {
        self.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    fn dnf(formula: &FOF) -> FOF {
        formula.pnf().snf().dnf().into()
    }

    #[test]
    fn test_dnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_string!("true", dnf(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_string!("false", dnf(&formula));
        }
        {
            let formula: FOF = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", dnf(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", dnf(&formula));
        }
        {
            let formula: FOF = "x=y".parse().unwrap();
            assert_debug_string!("x = y", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "((((~P(x)) & (~Q(y))) | ((~P(x)) & P(x))) | (Q(y) & (~Q(y)))) | (Q(y) & P(x))",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", dnf(&formula));
        }
        // quantifier-free formulae
        {
            let formula: FOF = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("((~P(x1)) & (~P(x2))) | (~Q(y))", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | (Q(x) & (~Q(y)))", dnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) & (~Q(y))) | R(z)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!(
                "(P(x) | (Q(x) & (~Q(y)))) | (Q(y) & (~Q(x)))",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!("(((((((~P(x)) & (~Q(y))) & (~R(z))) | (((~P(x)) & (~Q(y))) & P(x))) | (((~P(x)) & (~Q(y))) & Q(y))) | (R(z) & (~R(z)))) | (R(z) & P(x))) | (R(z) & Q(y))",                                 
                                dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!("(P(x) | Q(x)) | (R(y) & R(z))", dnf(&formula));
        }
        {
            let formula: FOF = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!("(P(x1) & P(x2)) | (Q(x1) & Q(x2))", dnf(&formula));
        }

        //random formulae
        {
            let formula: FOF = "?x. P(x)".parse().unwrap();
            assert_debug_string!("P('sk#0)", dnf(&formula));
        }
        {
            let formula: FOF = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('sk#0) & Q(f(), 'sk#0)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("((~P(y)) | (~Q(x, y))) | R(x)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("((~P(x)) | (~Q(y))) | (~R(x, y))", dnf(&formula));
        }
        {
            let formula: FOF = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, x)) & (~Q(x))) | Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, sk#0(y))) & (~Q(sk#0(y)))) | Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", dnf(&formula));
        }
        {
            let formula: FOF = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, sk#0(x))", dnf(&formula));
        }
        {
            let formula: FOF =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
                "(~R(z)) | ((P(sk#0(z), x) & (~Q(u`, x`, y))) & (~(w = f(u`))))",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!("(P(y) & (~Q(x, y))) | Q(sk#0(x, y), x)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(sk#0(x)) & (~Q(x, sk#0(x)))) | Q(sk#1(x), x)",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!("((P('sk#0) & (~Q('sk#0, y))) | (P('sk#0) & (y = z))) | (P('sk#0) & (~Q('sk#0, z)))",
                                dnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                .parse()
                .unwrap();
            assert_debug_string!("((~P(x)) | (((~P(y)) & Q(x, sk#0(x, y))) & (~P(sk#0(x, y))))) | ((P(f(x, y)) & Q(x, sk#0(x, y))) & (~P(sk#0(x, y))))",
                                 dnf(&formula));
        }
    }
}
