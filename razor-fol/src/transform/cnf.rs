/*! Defines formulae in Conjunctive Normal Form (CNF) and implements an algorithm for
converting [`SNF`] to [`CNF`].

[`SNF`]: crate::transform::SNF
 */

use super::{TermBased, SNF};
use crate::syntax::{formula::*, Complex, Error, Sig, FOF, V};
use itertools::Itertools;
use std::ops::Deref;

/// Is a [`CNF`] clause, representing disjunction of zero or more [`Literal`]s.
#[derive(Clone, Debug)]
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
        Self(vec![value])
    }
}

impl<I: IntoIterator<Item = Literal>> From<I> for Clause {
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Default for Clause {
    fn default() -> Self {
        Self::from(Vec::<Literal>::new())
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

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self(self.0.iter().map(|lit| lit.transform(f)).collect())
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
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
    }
}

/// Represents a formula in Conjunctive Normal Form (CNF).
///
/// **Hint**: A CNF is a firsts-order formula that is a conjunction of zero or
/// more [`Clause`]s.
#[derive(Clone, Debug)]
pub struct CNF(Vec<Clause>);

impl From<Clause> for CNF {
    fn from(value: Clause) -> Self {
        Self(vec![value])
    }
}

impl CNF {
    /// Consumes the receiver CNF and `other` and returns a CNF containing
    /// all clauses in the receiver and `other`.    
    pub fn union(self, other: Self) -> Self {
        let mut lits = self.0;
        lits.extend(other.0);
        lits.into()
    }

    /// Returns the clauses of the receiver CNF.
    pub fn clauses(&self) -> &[Clause] {
        &self.0
    }
}

impl Deref for CNF {
    type Target = [Clause];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<I: IntoIterator<Item = Clause>> From<I> for CNF {
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Default for CNF {
    fn default() -> Self {
        Self::from(Vec::<Clause>::new())
    }
}

impl From<&SNF> for CNF {
    fn from(value: &SNF) -> Self {
        // Compromising type safety to avoid implementing a number of
        // types arising from pairwise combinations of PNF, SNF and NNF:
        let nnf = FOF::from(value.clone()).nnf();
        cnf(distribute_or(&nnf.into()))
    }
}

impl TermBased for CNF {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = Vec::new();
        for clause in &self.0 {
            vs.extend(clause.free_vars());
        }
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self(self.0.iter().map(|clause| clause.transform(f)).collect())
    }
}

impl Formula for CNF {
    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }
}

impl From<CNF> for FOF {
    fn from(value: CNF) -> Self {
        value
            .0
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
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
        _ => unreachable!(), // `formula` is both in SNF and NNF
    }
}

// Eliminates the existential quantifiers of the input formula.
fn cnf(formula: FOF) -> CNF {
    match formula {
        FOF::Top => CNF::default(),
        FOF::Bottom => CNF::from(Clause::default()),
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
        FOF::And(this) => cnf(this.left).union(cnf(this.right)),
        FOF::Or(this) => {
            let mut left = cnf(this.left);
            let mut right = cnf(this.right);
            if left.0.is_empty() {
                left
            } else if right.0.is_empty() {
                right
            } else if left.0.len() == 1 && right.0.len() == 1 {
                let left = left.0.remove(0);
                let right = right.0.remove(0);
                left.union(right).into()
            } else {
                unreachable!() // Disjunction is distributed over conjunction in `formula`
            }
        }
        FOF::Forall(this) => cnf(this.formula),
        _ => unreachable!(), // `formula` is in SNF
    }
}

impl SNF {
    /// Transform the receiver SNF to a Conjunctive Normal Form (CNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
    /// let snf = formula.pnf().snf();
    /// let cnf = snf.cnf();
    /// assert_eq!("((¬P(x)) ∨ Q(y)) ∧ ((¬Q(y)) ∨ P(x))", FOF::from(cnf).to_string());
    /// ```
    pub fn cnf(&self) -> CNF {
        self.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    fn cnf(formula: &FOF) -> FOF {
        formula.pnf().snf().cnf().into()
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
            assert_debug_string!("(~P(x)) | Q(y)", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & ((~Q(y)) | P(x))", cnf(&formula));
        }
        {
            let formula: FOF = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", cnf(&formula));
        }
        // quantifier-free formulae
        {
            let formula: FOF = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("((~P(x1)) | (~Q(y))) & ((~P(x2)) | (~Q(y)))", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) | Q(x)) & (P(x) | (~Q(y)))", cnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) | R(z)) & ((~Q(y)) | R(z))", cnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("((((P(x) | Q(x)) | Q(y)) & ((P(x) | Q(x)) | (~Q(x)))) & ((P(x) | (~Q(y))) | Q(y))) & ((P(x) | (~Q(y))) | (~Q(x)))",
                                cnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) | R(z)) & ((~Q(y)) | R(z))) & (((~R(z)) | P(x)) | Q(y))",
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
            assert_debug_string!("P('sk#0)", cnf(&formula));
        }
        {
            let formula: FOF = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('sk#0) & Q(f(), 'sk#0)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("((~P(y)) | (~Q(x, y))) | R(x)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("((~P(x)) | (~Q(y))) | (~R(x, y))", cnf(&formula));
        }
        {
            let formula: FOF = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, x)) | Q(y)) & ((~Q(x)) | Q(y))", cnf(&formula));
        }
        {
            let formula: FOF = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "((~P(y, sk#0(y))) | Q(y)) & ((~Q(sk#0(y))) | Q(y))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", cnf(&formula));
        }
        {
            let formula: FOF = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, sk#0(x))", cnf(&formula));
        }
        {
            let formula: FOF =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!("(((~R(z)) | P(sk#0(z), x)) & ((~R(z)) | (~Q(u`, x`, y)))) & ((~R(z)) | (~(w = f(u`))))",             
                                cnf(&formula));
        }
        {
            let formula: FOF = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(y) | Q(sk#0(x, y), x)) & ((~Q(x, y)) | Q(sk#0(x, y), x))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(sk#0(x)) | Q(sk#1(x), x)) & ((~Q(x, sk#0(x))) | Q(sk#1(x), x))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "P('sk#0) & (((~Q('sk#0, y)) | (y = z)) | (~Q('sk#0, z)))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                .parse()
                .unwrap();
            assert_debug_string!("((((~P(x)) | (~P(y))) | P(f(x, y))) & ((~P(x)) | Q(x, sk#0(x, y)))) & ((~P(x)) | (~P(sk#0(x, y))))",
                                cnf(&formula));
        }
    }
}
