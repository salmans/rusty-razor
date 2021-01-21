/*! Defines formulae in Conjunctive Normal Form (CNF) and implements an algorithm for
converting [`SNF`] to [`CNF`].

[`SNF`]: crate::transform::SNF
 */

use super::{ToSNF, SNF};
use crate::syntax::{
    formula::{
        clause::{Clause, ClauseSet, Literal},
        *,
    },
    term::Complex,
    Error, Sig, Var, FOF,
};
use itertools::Itertools;
use std::{collections::BTreeSet, ops::Deref};

// CNF clauses and clause sets are constructed over complex terms.
type CNFClause = Clause<Complex>;
type CNFClauseSet = ClauseSet<Complex>;

/// Represents a formula in Conjunctive Normal Form (CNF).
///
/// **Hint**: A CNF is a firsts-order formula that is a conjunction of zero or
/// more [`Clause`]s where each clause is a disjunction of [`Literal`]s.
#[derive(Clone, Debug)]
pub struct CNF(CNFClauseSet);

impl From<CNFClauseSet> for CNF {
    fn from(value: CNFClauseSet) -> Self {
        Self(value)
    }
}

pub trait ToCNF: Formula {
    /// Transform the receiver formula to a Conjunctive Normal Form (CNF).
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

impl ToCNF for SNF {
    fn cnf(&self) -> CNF {
        use super::ToNNF;

        // Compromising type safety to avoid implementing a number of
        // types arising from pairwise combinations of PNF, SNF and NNF:
        let nnf = FOF::from(self.clone()).nnf();
        cnf(distribute_or(&nnf.into()))
    }
}

impl<T: ToSNF> ToCNF for T {
    fn cnf(&self) -> CNF {
        self.snf().cnf()
    }
}

impl<T: ToCNF> From<T> for CNF {
    fn from(value: T) -> Self {
        value.cnf()
    }
}

impl CNF {
    /// Returns the clauses of the receiver CNF.
    #[inline(always)]
    pub fn clauses(&self) -> &BTreeSet<CNFClause> {
        &self.0
    }

    /// Consumes the receiver and returns the underlying set of clauses.
    pub fn into_clauses(self) -> BTreeSet<CNFClause> {
        self.0.into_clauses()
    }

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

impl Deref for CNF {
    type Target = CNFClauseSet;

    fn deref(&self) -> &Self::Target {
        &self.0
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
        self.0.signature()
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.0.free_vars()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self(self.0.transform(f))
    }
}

impl From<CNF> for FOF {
    fn from(value: CNF) -> Self {
        value
            .into_clauses()
            .into_iter()
            .sorted()
            .into_iter()
            .map(CNF::clause_to_fof)
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

impl From<&CNF> for FOF {
    fn from(value: &CNF) -> Self {
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
        _ => unreachable!(), // `formula` is both in SNF and NNF
    }
}

fn cnf(formula: FOF) -> CNF {
    match formula {
        FOF::Top => CNF::default(),
        FOF::Bottom => ClauseSet::from(Clause::default()).into(),
        FOF::Atom(this) => {
            let clause = Clause::from(Literal::from(this));
            ClauseSet::from(clause).into()
        }
        FOF::Equals(this) => {
            let clause = Clause::from(Literal::from(this));
            ClauseSet::from(clause).into()
        }
        FOF::Not(this) => match this.formula {
            FOF::Atom(atom) => {
                let lit: Literal<_> = Not { formula: atom }.into();
                let clause = Clause::from(lit);
                ClauseSet::from(clause).into()
            }
            FOF::Equals(eq) => {
                let lit: Literal<_> = Not { formula: eq }.into();
                let clause = Clause::from(lit);
                ClauseSet::from(clause).into()
            }
            _ => unreachable!(), // `formula` is in NNF
        },
        FOF::And(this) => {
            let left = cnf(this.left);
            let right = cnf(this.right);
            left.0.union(&right.0).into()
        }
        FOF::Or(this) => {
            let left = cnf(this.left);
            let right = cnf(this.right);
            if left.0.is_empty() {
                left
            } else if right.0.is_empty() {
                right
            } else if left.0.len() == 1 && right.0.len() == 1 {
                let left = left.into_clauses().into_iter().next().unwrap();
                let right = right.into_clauses().into_iter().next().unwrap();
                let clause = left.union(&right);
                ClauseSet::from(clause).into()
            } else {
                unreachable!() // Disjunction is distributed over conjunction in `formula`
            }
        }
        FOF::Forall(this) => cnf(this.formula),
        _ => unreachable!(), // `formula` is in SNF
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
        formula.snf().cnf().into()
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
            assert_debug_string!("P(x)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", cnf(&formula));
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
            assert_debug_string!("P('c#0)", cnf(&formula));
        }
        {
            let formula: FOF = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('c#0) & Q(f(), 'c#0)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("(R(x) | ~P(y)) | ~Q(x, y)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x) | ~Q(y)) | ~R(x, y)", cnf(&formula));
        }
        {
            let formula: FOF = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("(Q(y) | ~P(y, x)) & (Q(y) | ~Q(x))", cnf(&formula));
        }
        {
            let formula: FOF = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "(Q(y) | ~P(y, f#0(y))) & (Q(y) | ~Q(f#0(y)))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", cnf(&formula));
        }
        {
            let formula: FOF = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", cnf(&formula));
        }
        {
            let formula: FOF = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, f#0(x))", cnf(&formula));
        }
        {
            let formula: FOF =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
                "((P(f#0(z), x) | ~R(z)) & (~Q(u`, x`, y) | ~R(z))) & (~R(z) | ~(w = f(u`)))",
                cnf(&formula)
            );
        }
        {
            let formula: FOF = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(y) | Q(f#0(x, y), x)) & (Q(f#0(x, y), x) | ~Q(x, y))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(f#0(x)) | Q(f#1(x), x)) & (Q(f#1(x), x) | ~Q(x, f#0(x)))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "P(\'c#0) & ((y = z | ~Q(\'c#0, y)) | ~Q(\'c#0, z))",
                cnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                .parse()
                .unwrap();
            assert_debug_string!(
        "(((P(f(x, y)) | ~P(x)) | ~P(y)) & (Q(x, f#0(x, y)) | ~P(x))) & (~P(x) | ~P(f#0(x, y)))", cnf(&formula));
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
            FOF::from(cnf.transform(&f))
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
