/*! Defines formulae in Disjunctive Normal Form (DNF) and implements an algorithm for
transforming an [`SNF`] to a [`DNF`].

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

// DNF clauses and clause sets are constructed over complex terms.
type DNFClause = Clause<Complex>;
type DNFClauseSet = ClauseSet<Complex>;

/// Represents a formula in Disjunctive Normal Form (DNF).
///
/// **Hint**: A DNF is a firsts-order formula that is a disjunction of zero or
/// more [`Clause`]s where each clause is a conjunction of [`Literal`]s.
#[derive(Clone)]
pub struct DNF(DNFClauseSet);

impl From<DNFClauseSet> for DNF {
    fn from(value: DNFClauseSet) -> Self {
        DNF(value)
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

impl ToDNF for SNF {
    fn dnf(&self) -> DNF {
        use super::ToNNF;

        // Compromising type safety to avoid implementing a number of
        // types arising from pairwise combinations of PNF, SNF and NNF:
        let nnf = FOF::from(self.clone()).nnf();
        dnf(distribute_and(&nnf.into()))
    }
}

impl<T: ToSNF> ToDNF for T {
    fn dnf(&self) -> DNF {
        self.snf().dnf()
    }
}

impl<T: ToDNF> From<T> for DNF {
    fn from(value: T) -> Self {
        value.dnf()
    }
}

impl DNF {
    /// Returns the clauses of `self`.
    #[inline(always)]
    pub fn clauses(&self) -> &BTreeSet<DNFClause> {
        &self.0
    }

    /// Consumes `self` and returns the underlying clauses.
    pub fn into_clauses(self) -> BTreeSet<DNFClause> {
        self.0.into_clauses()
    }

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

impl Deref for DNF {
    type Target = DNFClauseSet;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::fmt::Display for DNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl Default for DNF {
    fn default() -> Self {
        DNF::from(ClauseSet::<_>::default())
    }
}

impl Formula for DNF {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        self.0.signature()
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.0.free_vars()
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        DNF(self.0.transform_term(f))
    }
}

impl From<DNF> for FOF {
    fn from(value: DNF) -> Self {
        value
            .into_clauses()
            .into_iter()
            .sorted()
            .into_iter()
            .map(DNF::clause_to_fof)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
    }
}

impl From<&DNF> for FOF {
    fn from(value: &DNF) -> Self {
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
        _ => unreachable!(), // NNF input
    }
}

fn dnf(formula: FOF) -> DNF {
    match formula {
        FOF::Top => ClauseSet::from(Clause::default()).into(),
        FOF::Bottom => DNF::default(),
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
            let left = dnf(this.left);
            let right = dnf(this.right);
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
                unreachable!() // Conjunction is distributed over disjunction in `formula`
            }
        }
        FOF::Or(this) => {
            let left = dnf(this.left);
            let right = dnf(this.right);
            left.0.union(&right.0).into()
        }
        FOF::Forall(this) => dnf(this.formula),
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

    fn dnf(formula: &FOF) -> FOF {
        formula.snf().dnf().into()
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
            assert_debug_string!("Q(y) | ~P(x)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "(((P(x) & Q(y)) | (P(x) & ~P(x))) | (Q(y) & ~Q(y))) | (~P(x) & ~Q(y))",
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
            assert_debug_string!("(~P(x1) & ~P(x2)) | ~Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | (Q(x) & ~Q(y))", dnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("R(z) | (~P(x) & ~Q(y))", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) | (Q(x) & ~Q(y))) | (Q(y) & ~Q(x))", dnf(&formula),);
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!("(((((P(x) & R(z)) | ((P(x) & ~P(x)) & ~Q(y))) | (Q(y) & R(z))) | ((Q(y) & ~P(x)) & ~Q(y))) | (R(z) & ~R(z))) | ((~P(x) & ~Q(y)) & ~R(z))",
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
            assert_debug_string!("P('c#0)", dnf(&formula));
        }
        {
            let formula: FOF = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('c#0) & Q(f(), 'c#0)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("(R(x) | ~P(y)) | ~Q(x, y)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x) | ~Q(y)) | ~R(x, y)", dnf(&formula));
        }
        {
            let formula: FOF = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("Q(y) | (~P(y, x) & ~Q(x))", dnf(&formula));
        }
        {
            let formula: FOF = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!("Q(y) | (~P(y, f#0(y)) & ~Q(f#0(y)))", dnf(&formula));
        }
        {
            let formula: FOF = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", dnf(&formula));
        }
        {
            let formula: FOF = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('c#0, 'c#1)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, f#0(x))", dnf(&formula));
        }
        {
            let formula: FOF =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
                "((P(f#0(z), x) & ~Q(u`, x`, y)) & ~(w = f(u`))) | ~R(z)",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!("(P(y) & ~Q(x, y)) | Q(f#0(x, y), x)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!("(P(f#0(x)) & ~Q(x, f#0(x))) | Q(f#1(x), x)", dnf(&formula),);
        }
        {
            let formula: FOF = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "((P(\'c#0) & y = z) | (P(\'c#0) & ~Q(\'c#0, y))) | (P(\'c#0) & ~Q(\'c#0, z))",
                dnf(&formula)
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                .parse()
                .unwrap();
            assert_debug_string!("(((P(f(x, y)) & Q(x, f#0(x, y))) & ~P(f#0(x, y))) | ((Q(x, f#0(x, y)) & ~P(y)) & ~P(f#0(x, y)))) | ~P(x)", dnf(&formula));
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
            let cnf = fof!({ P(x, x) } | { P(x) }).dnf();
            assert!(cnf.signature().is_err());
        }
    }
}
