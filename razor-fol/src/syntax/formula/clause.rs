use super::{Atom, Atomic, Equals, Formula, FormulaEx, Not};
use crate::syntax::{Error, Sig, Term, Var};
use itertools::Itertools;
use std::{collections::BTreeSet, hash::Hash, iter::FromIterator, ops::Deref};

/// A literal is either an [`Atomic`] formula or its negation.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Literal<T: Term> {
    /// Wraps an (positive) [`Atomic`] formula.
    Pos(Atomic<T>),

    /// Wraps the negation of an [`Atomic`] formula.    
    Neg(Atomic<T>),
}

impl<T: Term> From<Atomic<T>> for Literal<T> {
    fn from(value: Atomic<T>) -> Self {
        Self::Pos(value)
    }
}

impl<T: Term> From<Not<Atomic<T>>> for Literal<T> {
    fn from(value: Not<Atomic<T>>) -> Self {
        Self::Neg(value.formula)
    }
}

impl<T: Term> From<Atom<T>> for Literal<T> {
    fn from(value: Atom<T>) -> Self {
        Self::Pos(value.into())
    }
}

impl<T: Term> From<Not<Atom<T>>> for Literal<T> {
    fn from(value: Not<Atom<T>>) -> Self {
        Self::Neg(value.formula.into())
    }
}

impl<T: Term> From<Equals<T>> for Literal<T> {
    fn from(value: Equals<T>) -> Self {
        Self::Pos(value.into())
    }
}

impl<T: Term> From<Not<Equals<T>>> for Literal<T> {
    fn from(value: Not<Equals<T>>) -> Self {
        Self::Neg(value.formula.into())
    }
}

impl<T: Term> Formula for Literal<T> {
    type Term = T;

    fn signature(&self) -> Result<Sig, Error> {
        match self {
            Literal::Pos(this) | Literal::Neg(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&Var> {
        match self {
            Literal::Pos(this) | Literal::Neg(this) => this.free_vars(),
        }
    }

    fn transform_term(&self, f: &impl Fn(&T) -> T) -> Self {
        match self {
            Literal::Pos(this) => Self::Pos(this.transform_term(f)),
            Literal::Neg(this) => Self::Neg(this.transform_term(f)),
        }
    }
}

impl<T: Term> FormulaEx for Literal<T> {
    fn precedence(&self) -> u8 {
        match self {
            Literal::Pos(this) | Literal::Neg(this) => this.precedence(),
        }
    }
}

/// Represents a collection of [`Literal`]s.
///
/// **Note:**
/// The interpretation of a clause depends on its syntactic context.
/// For example, a [`CNF`] clause is interpreted as disjunction of literals whereas
/// a [`DNF`] clause corresponds to a conjunction of literals.
///
/// [`CNF`]: crate::transform::CNF
/// [`DNF`]: crate::transform::DNF
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct Clause<T: Term>(BTreeSet<Literal<T>>);

impl<T: Term> Clause<T> {
    /// Returns the literals of `self` clause.
    pub fn literals(&self) -> &BTreeSet<Literal<T>> {
        &self.0
    }

    /// Consumes `self` and returns its underlying list of [`Literal`]s.
    pub fn into_literals(self) -> BTreeSet<Literal<T>> {
        self.0
    }
}

impl<T: Term + Ord + Clone> Clause<T> {
    /// Returns a clause containing all literals in `self` and `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().collect()
    }
}

impl<T: Term> Deref for Clause<T> {
    type Target = BTreeSet<Literal<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Term + Ord> From<Literal<T>> for Clause<T> {
    fn from(value: Literal<T>) -> Self {
        vec![value].into_iter().collect()
    }
}

impl<T> FromIterator<Literal<T>> for Clause<T>
where
    T: Term + Ord,
{
    fn from_iter<I: IntoIterator<Item = Literal<T>>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<T> IntoIterator for Clause<T>
where
    T: Term,
{
    type Item = Literal<T>;

    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> From<Vec<Literal<T>>> for Clause<T>
where
    T: Term + Ord,
{
    fn from(value: Vec<Literal<T>>) -> Self {
        Self(value.into_iter().collect())
    }
}

impl<T: Term + Ord> Default for Clause<T> {
    fn default() -> Self {
        Self(BTreeSet::new())
    }
}

impl<T: Term + Ord> Formula for Clause<T> {
    type Term = T;

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

    fn transform_term(&self, f: &impl Fn(&T) -> T) -> Self {
        self.0.iter().map(|lit| lit.transform_term(f)).collect()
    }
}

/// Represents a set of [`Clause`]s.
///
/// **Note:**
/// The interpretation of a clause set depends on its syntactic context. For example,
/// a [`CNF`] is a clause set that is interpreted as a conjunction of clauses where each
/// clause is a disjunction of literals. In contrast, a [`DNF`] is a clause set that
/// corresponds to a disjunction of clauses where each clause is a conjunction of literals.
///
/// [`CNF`]: crate::transform::CNF
/// [`DNF`]: crate::transform::DNF
#[derive(PartialEq, Clone, Debug)]
pub struct ClauseSet<T: Term>(BTreeSet<Clause<T>>);

impl<T: Term + Ord> From<Clause<T>> for ClauseSet<T> {
    fn from(value: Clause<T>) -> Self {
        vec![value].into()
    }
}

impl<T> FromIterator<Clause<T>> for ClauseSet<T>
where
    T: Term + Ord,
{
    fn from_iter<I: IntoIterator<Item = Clause<T>>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<T> IntoIterator for ClauseSet<T>
where
    T: Term + Ord,
{
    type Item = Clause<T>;

    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> From<Vec<Clause<T>>> for ClauseSet<T>
where
    T: Term + Ord,
{
    fn from(value: Vec<Clause<T>>) -> Self {
        value.into_iter().collect()
    }
}

impl<T: Term> ClauseSet<T> {
    /// Returns the clauses of `self`.
    pub fn clauses(&self) -> &BTreeSet<Clause<T>> {
        &self.0
    }

    /// Consumes `self` and returns its underlying set of clauses.
    pub fn into_clauses(self) -> BTreeSet<Clause<T>> {
        self.0
    }
}

impl<T: Term + Ord + Clone> ClauseSet<T> {
    /// Returns a clause set, containing all clauses in `self` and `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().collect()
    }

    /// Returns a new clause set obtained by removing clauses that are proper supersets of
    /// some other clauses in the clause set.
    pub fn minimize(&self) -> Self {
        self.iter()
            .filter(|c1| !self.iter().any(|c2| *c1 != c2 && c2.is_subset(c1)))
            .cloned()
            .collect()
    }

    /// Returns a new clause set obtained by removing clauses that are proper subsets of
    /// some other clauses in the clause set.
    pub fn maximize(&self) -> Self {
        self.iter()
            .filter(|c1| !self.iter().any(|c2| *c1 != c2 && c2.is_superset(c1)))
            .cloned()
            .collect()
    }
}

impl<T: Term> Deref for ClauseSet<T> {
    type Target = BTreeSet<Clause<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Term + Ord> Default for ClauseSet<T> {
    fn default() -> Self {
        Self(BTreeSet::new())
    }
}

impl<T: Term + Ord> Formula for ClauseSet<T> {
    type Term = T;

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

    fn transform_term(&self, f: &impl Fn(&T) -> T) -> Self {
        self.0
            .iter()
            .map(|clause| clause.transform_term(f))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assert_eq_sorted_vecs,
        syntax::{
            signature::{FuncSig, PredSig},
            term::Complex,
            Const, Func, Pred, Sig, EQ_SYM,
        },
        term, v,
    };

    #[test]
    fn literal_free_vars() {
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x), term!(y)],
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Literal::from(Equals {
                    left: term!(x),
                    right: term!(y),
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Literal::from(Not {
                    formula: Atom {
                        predicate: "R".into(),
                        terms: vec![term!(x), term!(y)],
                    }
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Literal::from(Not {
                    formula: Equals {
                        left: term!(x),
                        right: term!(y),
                    }
                })
                .free_vars()
            );
        }
    }

    #[test]
    fn atomic_transform() {
        {
            let formula: Literal<_> = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(y)],
            }
            .into();
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
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z), term!(y)],
                }),
                formula.transform_term(&f)
            );
        }
        {
            let formula: Literal<_> = Not {
                formula: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x)), term!(y)],
                },
            }
            .into();
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
                Literal::from(Not {
                    formula: Atom {
                        predicate: "P".into(),
                        terms: vec![term!(z), term!(y)],
                    }
                }),
                formula.transform_term(&f)
            );
        }
        {
            let formula: Literal<_> = Equals {
                left: term!(f(x)),
                right: term!(y),
            }
            .into();
            let f = |t: &Complex| {
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
            };
            assert_eq!(
                Literal::from(Equals {
                    left: term!(z),
                    right: term!(y),
                }),
                formula.transform_term(&f)
            );
        }
        {
            let formula: Literal<_> = Not {
                formula: Equals {
                    left: term!(f(x)),
                    right: term!(y),
                },
            }
            .into();
            let f = |t: &Complex| {
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
            };
            assert_eq!(
                Literal::from(Not {
                    formula: Equals {
                        left: term!(z),
                        right: term!(y),
                    }
                }),
                formula.transform_term(&f)
            );
        }
    }

    #[test]
    fn atomic_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: Literal<_> = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x, @c))],
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: Literal<_> = Not {
                formula: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x, @c))],
                },
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: Literal<_> = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(f(x, y))],
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Literal<_> = Not {
                formula: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x)), term!(f(x, y))],
                },
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from(EQ_SYM),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: Literal<_> = Equals {
                left: term!(@c),
                right: term!(@c),
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from(EQ_SYM),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: Literal<_> = Not {
                formula: Equals {
                    left: term!(@c),
                    right: term!(@c),
                },
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: Literal<_> = Equals {
                left: term!(f(x)),
                right: term!(f(x, y)),
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Literal<_> = Not {
                formula: Equals {
                    left: term!(f(x)),
                    right: term!(f(x, y)),
                },
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Literal<_> = Not {
                formula: Equals {
                    left: term!(f(x)),
                    right: term!(f(x)),
                },
            }
            .into();
            assert!(formula.signature().is_ok());
        }
    }

    #[test]
    fn clause_free_vars() {
        let expected = vec![v!(x), v!(y)];
        let clause: Clause<_> = vec![
            Literal::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(y)],
            }),
            Literal::from(Atom {
                predicate: "Q".into(),
                terms: vec![term!(x)],
            }),
        ]
        .into();
        assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), clause.free_vars());
    }

    #[test]
    fn clause_union() {
        {
            let first: Clause<_> = vec![Literal::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(y)],
            })]
            .into();
            let second = Clause::default();

            assert_eq!(first, first.union(&second));
            assert_eq!(first, second.union(&first));
        }
        {
            let first: Clause<_> = vec![
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                }),
                Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }),
            ]
            .into();
            let second: Clause<_> = vec![
                Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![],
                }),
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                }),
            ]
            .into();
            let expected: Clause<_> = vec![
                Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }),
                Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![],
                }),
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                }),
            ]
            .into();

            assert_eq!(expected, first.union(&second));
            assert_eq!(expected, second.union(&first));
        }
    }

    #[test]
    fn clause_transform() {
        {
            let clause: Clause<_> = vec![
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                }),
                Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x))],
                }),
            ]
            .into();
            let expected: Clause<_> = vec![
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                }),
                Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(z)],
                }),
            ]
            .into();

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
            assert_eq!(expected, clause.transform_term(&f));
        }
    }

    #[test]
    fn clause_signature() {
        {
            let clause: Clause<_> = vec![
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(@c)), term!(y)],
                }),
                Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x))],
                }),
            ]
            .into();
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));

            assert_eq!(sig, clause.signature().unwrap());
        }
        {
            let clause: Clause<_> = vec![
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(@c, y)), term!(y)],
                }),
                Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x))],
                }),
            ]
            .into();
            assert!(clause.signature().is_err());
        }
        {
            let clause: Clause<_> = vec![
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(@c))],
                }),
                Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }),
            ]
            .into();
            assert!(clause.signature().is_ok());
        }
    }

    #[test]
    fn clause_set_free_vars() {
        let expected = vec![v!(x), v!(y)];
        let clause: ClauseSet<_> = vec![
            Clause::from(Literal::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(y)],
            })),
            Clause::from(Literal::from(Atom {
                predicate: "Q".into(),
                terms: vec![term!(x)],
            })),
        ]
        .into();
        assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), clause.free_vars());
    }

    #[test]
    fn clause_set_transform() {
        {
            let clause_set: ClauseSet<_> = vec![
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x))],
                })),
            ]
            .into();
            let expected: ClauseSet<_> = vec![
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(z)],
                })),
            ]
            .into();

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
            assert_eq!(expected, clause_set.transform_term(&f));
        }
    }

    #[test]
    fn clause_set_signature() {
        {
            let clause_set: ClauseSet<_> = vec![
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(@c)), term!(y)],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x))],
                })),
            ]
            .into();
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));

            assert_eq!(sig, clause_set.signature().unwrap());
        }
        {
            let clause_set: ClauseSet<_> = vec![
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(@c, y)), term!(y)],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x))],
                })),
            ]
            .into();
            assert!(clause_set.signature().is_err());
        }
        {
            let clause_set: ClauseSet<_> = vec![
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(@c))],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                })),
            ]
            .into();
            assert!(clause_set.signature().is_ok());
        }
    }

    #[test]
    fn clause_set_union() {
        {
            let first: ClauseSet<_> = vec![Clause::from(Literal::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(y)],
            }))]
            .into();
            let second = ClauseSet::default();

            assert_eq!(first, first.union(&second));
            assert_eq!(first, second.union(&first));
        }
        {
            let first: ClauseSet<_> = vec![
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                })),
            ]
            .into();
            let second: ClauseSet<_> = vec![
                Clause::from(Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                })),
            ]
            .into();
            let expected: ClauseSet<_> = vec![
                Clause::from(Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![],
                })),
                Clause::from(Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(y)],
                })),
            ]
            .into();

            assert_eq!(expected, first.union(&second));
            assert_eq!(expected, second.union(&first));
        }
    }

    #[test]
    fn clause_set_minimize() {
        {
            let clause_set = ClauseSet::<Complex>::default();
            assert_eq!(clause_set, clause_set.minimize());
        }
        {
            let clause_set: ClauseSet<_> = vec![Clause::from(vec![Literal::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(x)],
            })])]
            .into();
            assert_eq!(clause_set, clause_set.minimize());
        }
        {
            let clause_set: ClauseSet<_> = vec![
                Clause::from(vec![
                    Literal::from(Atom {
                        predicate: "P".into(),
                        terms: vec![term!(x)],
                    }),
                    Literal::from(Atom {
                        predicate: "Q".into(),
                        terms: vec![term!(x)],
                    }),
                ]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                })]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                })]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                })]),
            ]
            .into();
            let expected: ClauseSet<_> = vec![
                Clause::from(vec![Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                })]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                })]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                })]),
            ]
            .into();
            assert_eq!(expected, clause_set.minimize());
        }
    }

    #[test]
    fn clause_set_maximize() {
        {
            let clause_set = ClauseSet::<Complex>::default();
            assert_eq!(clause_set, clause_set.maximize());
        }
        {
            let clause_set: ClauseSet<_> = vec![Clause::from(vec![Literal::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(x)],
            })])]
            .into();
            assert_eq!(clause_set, clause_set.maximize());
        }
        {
            let clause_set: ClauseSet<_> = vec![
                Clause::from(vec![
                    Literal::from(Atom {
                        predicate: "P".into(),
                        terms: vec![term!(x)],
                    }),
                    Literal::from(Atom {
                        predicate: "Q".into(),
                        terms: vec![term!(x)],
                    }),
                ]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                })]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                })]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                })]),
            ]
            .into();
            let expected: ClauseSet<_> = vec![
                Clause::from(vec![
                    Literal::from(Atom {
                        predicate: "P".into(),
                        terms: vec![term!(x)],
                    }),
                    Literal::from(Atom {
                        predicate: "Q".into(),
                        terms: vec![term!(x)],
                    }),
                ]),
                Clause::from(vec![Literal::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                })]),
            ]
            .into();
            assert_eq!(expected, clause_set.maximize());
        }
    }
}
