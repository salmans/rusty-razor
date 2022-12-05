/*! Defines formulae in Geometric Normal Form (GNF) and implements an algorithm for
transforming a [`CNFClauseSet`] to a [`GNF`].

[`CNFClauseSet`]: crate::transform::CNFClauseSet
*/
use super::{ToSNF, SNF};
use crate::syntax::{
    formula::{
        clause::{Clause, Literal},
        *,
    },
    term::Complex,
    Error, Sig, Var, FOF,
};
use itertools::Itertools;
use std::{collections::BTreeSet, convert::TryFrom, iter::FromIterator, ops::Deref};

// A positive literal is simply an atomic formula.
type PosLiteral = Atomic<Complex>;

/// A Positive Conjunctive Formula (PCF) represents a collection of [`Atomic`]s, interpreted
/// as a conjunction of positive literals. PCFs are the building blocks of [`GNF`]s.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Debug)]
pub struct PCF(BTreeSet<PosLiteral>);

impl PCF {
    /// Returns the positive literals of `self`.
    #[inline(always)]
    pub fn literals(&self) -> &BTreeSet<PosLiteral> {
        &self.0
    }

    /// Consumes `self` and returns its underlying list of positive literals.
    pub fn into_literals(self) -> BTreeSet<PosLiteral> {
        self.0
    }

    /// Returns a new clause, resulting from joining the positive literals of `self`
    /// and `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().collect()
    }
}

impl Deref for PCF {
    type Target = BTreeSet<PosLiteral>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<PosLiteral> for PCF {
    fn from(value: PosLiteral) -> Self {
        vec![value].into_iter().collect()
    }
}

impl From<Atom<Complex>> for PCF {
    fn from(value: Atom<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().collect()
    }
}

impl From<Equals<Complex>> for PCF {
    fn from(value: Equals<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().collect()
    }
}

impl FromIterator<PosLiteral> for PCF {
    fn from_iter<T: IntoIterator<Item = PosLiteral>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for PCF {
    type Item = PosLiteral;

    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl From<Vec<PosLiteral>> for PCF {
    fn from(value: Vec<PosLiteral>) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Formula for PCF {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.iter()
            .flat_map(|lit| lit.free_vars())
            .unique()
            .collect()
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        self.iter().map(|lit| lit.transform_term(f)).collect()
    }
}

impl From<PCF> for FOF {
    fn from(value: PCF) -> Self {
        value
            .into_literals()
            .into_iter()
            .sorted()
            .into_iter()
            .map(|atomic| match atomic {
                Atomic::Atom(this) => FOF::from(this),
                Atomic::Equals(this) => this.into(),
            })
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

impl From<&PCF> for FOF {
    fn from(value: &PCF) -> Self {
        value.clone().into()
    }
}

impl TryFrom<FOF> for PCF {
    type Error = super::Error;

    fn try_from(value: FOF) -> Result<Self, Self::Error> {
        match value {
            FOF::Top => Ok(Self::default()),
            FOF::Atom(atom) => Ok(Self::from(atom)),
            FOF::Equals(equals) => Ok(Self::from(equals)),
            FOF::And(and) => {
                let mut result = Self::try_from(and.left)?.into_literals();
                result.extend(Self::try_from(and.right)?.into_literals());
                Ok(result.into_iter().collect())
            }
            _ => Err(Self::Error::FofToGnf {
                formula: value.clone(),
            }),
        }
    }
}

/// Is a set of [`PCF`]s in the head of a [`GNF`], interpreted as a disjunction of
/// PCFs where each PCF is a conjunction of positive literals.
#[derive(PartialEq, Eq, Clone, Default, Debug)]
pub struct PcfSet(BTreeSet<PCF>);

impl PcfSet {
    /// Returns the clauses of `self`.
    #[inline(always)]
    pub fn clauses(&self) -> &BTreeSet<PCF> {
        &self.0
    }

    /// Consumes `self` and returns its underlying set of clauses.
    pub fn into_clauses(self) -> BTreeSet<PCF> {
        self.0
    }

    /// Returns a new positive clause set, containing clauses obtained by pairwise unioning
    /// of the clauses in `self` and `other`.
    pub fn cross_union(&self, other: &Self) -> Self {
        self.iter()
            .flat_map(|h1| other.iter().map(move |h2| h1.union(h2)))
            .collect()
    }

    /// Returns a new PCF set obtained by removing pcfs that are proper supersets of
    /// some other pcfs in `self`.
    pub fn simplify(&self) -> Self {
        self.iter()
            .filter(|c1| !self.iter().any(|c2| *c1 != c2 && c2.is_subset(c1)))
            .cloned()
            .collect()
    }
}

impl From<PCF> for PcfSet {
    fn from(value: PCF) -> Self {
        vec![value].into_iter().collect()
    }
}

impl FromIterator<PCF> for PcfSet {
    fn from_iter<T: IntoIterator<Item = PCF>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for PcfSet {
    type Item = PCF;

    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl From<Vec<PCF>> for PcfSet {
    fn from(value: Vec<PCF>) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Deref for PcfSet {
    type Target = BTreeSet<PCF>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Formula for PcfSet {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.iter()
            .flat_map(|lit| lit.free_vars())
            .unique()
            .collect()
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        self.iter().map(|lit| lit.transform_term(f)).collect()
    }
}

impl From<PcfSet> for FOF {
    fn from(value: PcfSet) -> Self {
        value
            .into_clauses()
            .into_iter()
            .sorted()
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
    }
}

impl From<&PcfSet> for FOF {
    fn from(value: &PcfSet) -> Self {
        value.clone().into()
    }
}

/// Represents a formula in Geometric Normal Form (GNF), consisting of a [`PCF`] in the body
/// (premise) and a [`PcfSet`] in the head (consequence).
///
/// **Hint**: For mor information about GNF, see [Geometric Logic in Computer Science][glics]
/// by Steve Vickers.
///
/// [glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
/// [`FOF`]: crate::syntax::FOF
#[derive(Clone, Debug)]
pub struct GNF {
    /// Is the body of a GNF, comprised of a positive clause.
    body: PCF,

    /// Is the head of a GNF, consisting of a positive clause set.
    head: PcfSet,
}

impl GNF {
    /// Returns the body of `self`.
    #[inline(always)]
    pub fn body(&self) -> &PCF {
        &self.body
    }

    /// Returns the head of `self`.
    #[inline(always)]
    pub fn head(&self) -> &PcfSet {
        &self.head
    }

    /// Consumes `self` and returns its body and head.
    pub fn into_body_and_head(self) -> (PCF, PcfSet) {
        (self.body, self.head)
    }
}

impl From<(PCF, PcfSet)> for GNF {
    fn from(value: (PCF, PcfSet)) -> Self {
        let (body, head) = value;
        Self { body, head }
    }
}

impl TryFrom<FOF> for PcfSet {
    type Error = super::Error;

    fn try_from(value: FOF) -> Result<Self, Self::Error> {
        match value {
            FOF::Top | FOF::Atom(_) | FOF::Equals(_) | FOF::And(_) => {
                PCF::try_from(value).map(Self::from)
            }
            FOF::Bottom => Ok(Self::default()),
            FOF::Or(or) => {
                let mut result = Self::try_from(or.left)?.into_clauses();
                result.extend(Self::try_from(or.right)?.into_clauses());
                Ok(result.into_iter().collect())
            }
            _ => Err(Self::Error::FofToGnf {
                formula: value.clone(),
            }),
        }
    }
}

/// Is the trait of [`Formula`] types that can be transformed to a list of [`GNF`]s.
pub trait ToGNF: Formula {
    /// Transforms `self` to a list of formulae in Geometric Normal
    /// Form (GNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToGNF;
    ///
    /// let formula: FOF = "P(x) & (Q(x) | R(x))".parse().unwrap();
    /// let gnfs = formula.gnf();
    ///  
    /// let gnf_to_string: Vec<String> = gnfs
    ///     .into_iter()
    ///     .map(|f| f.to_string())
    ///     .collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    fn gnf(&self) -> Vec<GNF>;
}

impl ToGNF for SNF {
    fn gnf(&self) -> Vec<GNF> {
        use super::ToCNFClauseSet;

        let clauses = self.cnf_clause_set();
        clauses.iter().map(gnf).collect()
    }
}

impl<T: ToSNF> ToGNF for T {
    fn gnf(&self) -> Vec<GNF> {
        self.snf().gnf()
    }
}

impl Formula for GNF {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        let sig = self.body().signature()?;
        sig.merge(self.head().signature()?)
    }

    fn free_vars(&self) -> Vec<&Var> {
        let mut b_vars = self.body.free_vars();
        b_vars.extend(self.head.free_vars());
        b_vars.into_iter().unique().collect()
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            body: self.body.transform_term(f),
            head: self.head.transform_term(f),
        }
    }
}

impl std::fmt::Display for GNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl From<GNF> for FOF {
    fn from(value: GNF) -> Self {
        let body = FOF::from(value.body);
        let head = FOF::from(value.head);
        body.implies(head)
    }
}

impl From<&GNF> for FOF {
    fn from(value: &GNF) -> Self {
        value.clone().into()
    }
}

impl TryFrom<FOF> for GNF {
    type Error = super::Error;

    fn try_from(value: FOF) -> Result<Self, Self::Error> {
        match value {
            FOF::Top => {
                let body = PCF::default();
                let head = PcfSet::from(PCF::default());
                Ok((body, head).into())
            }
            FOF::Bottom => {
                let body = PCF::default();
                let head = PcfSet::default();
                Ok((body, head).into())
            }
            FOF::Atom(_) | FOF::Equals(_) | FOF::And(_) | FOF::Or(_) => {
                let head = PcfSet::try_from(value)?;
                Ok((PCF::default(), head).into())
            }
            FOF::Implies(implies) => {
                let body = PCF::try_from(implies.premise)?;
                let head = PcfSet::try_from(implies.consequence)?;
                Ok((body, head).into())
            }
            _ => Err(Self::Error::FofToGnf {
                formula: value.clone(),
            }),
        }
    }
}

// Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
fn gnf(clause: &Clause<Complex>) -> GNF {
    let mut head: Vec<PCF> = Vec::new();
    let mut body: Vec<Atomic<_>> = Vec::new();
    clause.iter().for_each(|lit| match lit {
        Literal::Pos(this) => head.push(this.clone().into()),
        Literal::Neg(this) => body.push(this.clone()),
    });

    let body = PCF::from(body);
    let head = PcfSet::from(head);
    (body, head).into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assert_debug_strings, assert_eq_sorted_vecs, fof,
        syntax::{
            signature::{FuncSig, PredSig},
            Sig, EQ_SYM,
        },
        term, v,
    };
    use itertools::Itertools;

    fn gnf(formula: &FOF) -> Vec<FOF> {
        formula.gnf().into_iter().map(|gnf| gnf.into()).collect()
    }

    #[test]
    fn pcf_union() {
        {
            let first = PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            });
            let second = PCF::default();
            assert_eq!(first, first.union(&second));
            assert_eq!(first, second.union(&first));
        }
        {
            let first = PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            });
            let second = PCF::from(vec![
                Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![],
                }
                .into(),
            ]);
            let expected = PCF::from(vec![
                Atom {
                    predicate: "P".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![],
                }
                .into(),
            ]);
            assert_eq!(expected, first.union(&second));
            assert_eq!(expected, second.union(&first));
        }
    }

    #[test]
    fn pcf_free_vars() {
        {
            let pcf = PCF::default();
            assert_eq!(Vec::<&Var>::new(), pcf.free_vars());
        }
        {
            let pcf = PCF::from(vec![
                Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![term!(@c), term!(y)],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                }
                .into(),
            ]);
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), pcf.free_vars());
        }
    }

    #[test]
    fn pcf_transform() {
        {
            let pcf: PCF = Atomic::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(y)],
            })
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
                PCF::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z), term!(y)],
                }),
                pcf.transform_term(&f)
            );
        }
        {
            let pcf: PCF = Equals {
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
                PCF::from(Equals {
                    left: term!(z),
                    right: term!(y),
                }),
                pcf.transform_term(&f)
            );
        }
    }

    #[test]
    fn pcf_signature() {
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

            let pcf = PCF::from(vec![
                Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                Equals {
                    left: term!(f(x, @c)),
                    right: term!(y),
                }
                .into(),
                Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x, y)), term!(x)],
                }
                .into(),
            ]);
            assert_eq!(sig, pcf.signature().unwrap());
        }
        {
            let pcf = PCF::from(vec![
                Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .into(),
            ]);
            assert!(pcf.signature().is_err());
        }
    }

    #[test]
    fn pcf_set_cross_union() {
        {
            let first = PcfSet::default();
            let second = PcfSet::default();
            assert_eq!(PcfSet::default(), first.cross_union(&second));
        }
        {
            let first = PcfSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            let second = PcfSet::default();
            assert_eq!(PcfSet::default(), first.cross_union(&second));
            assert_eq!(PcfSet::default(), second.cross_union(&first));
        }
        {
            let first = PcfSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            let second = PcfSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            assert_eq!(first, first.cross_union(&second));
        }
        {
            let first = PcfSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            let second = PcfSet::from(vec![PCF::from(Atom {
                predicate: "Q".into(),
                terms: vec![],
            })]);
            let expected = PcfSet::from(vec![PCF::from(vec![
                Atom {
                    predicate: "P".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
            ])]);
            assert_eq!(expected, first.cross_union(&second));
            assert_eq!(expected, second.cross_union(&first));
        }
        {
            let first = PcfSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            let second = PcfSet::from(vec![PCF::from(vec![
                Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![],
                }
                .into(),
            ])]);
            let expected = PcfSet::from(vec![PCF::from(vec![
                Atom {
                    predicate: "P".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![],
                }
                .into(),
            ])]);
            assert_eq!(expected, first.cross_union(&second));
            assert_eq!(expected, second.cross_union(&first));
        }
        {
            let first = PcfSet::from(vec![
                PCF::from(Atomic::from(Atom {
                    predicate: "P".into(),
                    terms: vec![],
                })),
                PCF::from(Atomic::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                })),
            ]);
            let second = PcfSet::from(vec![
                PCF::from(Atomic::from(Atom {
                    predicate: "R".into(),
                    terms: vec![],
                })),
                PCF::from(Atomic::from(Atom {
                    predicate: "S".into(),
                    terms: vec![],
                })),
            ]);
            let expected = PcfSet::from(vec![
                PCF::from(vec![
                    Atomic::from(Atom {
                        predicate: "P".into(),
                        terms: vec![],
                    }),
                    Atom {
                        predicate: "R".into(),
                        terms: vec![],
                    }
                    .into(),
                ]),
                PCF::from(vec![
                    Atomic::from(Atom {
                        predicate: "P".into(),
                        terms: vec![],
                    }),
                    Atom {
                        predicate: "S".into(),
                        terms: vec![],
                    }
                    .into(),
                ]),
                PCF::from(vec![
                    Atomic::from(Atom {
                        predicate: "Q".into(),
                        terms: vec![],
                    }),
                    Atom {
                        predicate: "R".into(),
                        terms: vec![],
                    }
                    .into(),
                ]),
                PCF::from(vec![
                    Atomic::from(Atom {
                        predicate: "Q".into(),
                        terms: vec![],
                    }),
                    Atom {
                        predicate: "S".into(),
                        terms: vec![],
                    }
                    .into(),
                ]),
            ]);
            assert_eq!(expected, first.cross_union(&second));
            assert_eq!(expected, second.cross_union(&first));
        }
    }

    #[test]
    fn pcf_set_simplify() {
        {
            let pcf_set = PcfSet::default();
            assert_eq!(pcf_set, pcf_set.simplify());
        }
        {
            let pcf_set: PcfSet = vec![PCF::from(vec![Atomic::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(x)],
            })])]
            .into();
            assert_eq!(pcf_set, pcf_set.simplify());
        }
        {
            let pcf_set: PcfSet = vec![
                PCF::from(vec![
                    Atomic::from(Atom {
                        predicate: "P".into(),
                        terms: vec![term!(x)],
                    }),
                    Atom {
                        predicate: "Q".into(),
                        terms: vec![term!(x)],
                    }
                    .into(),
                ]),
                PCF::from(vec![Atomic::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                })]),
                PCF::from(vec![Atomic::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                })]),
                PCF::from(vec![Atomic::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                })]),
            ]
            .into();
            let expected: PcfSet = vec![
                PCF::from(vec![Atomic::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                })]),
                PCF::from(vec![Atomic::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                })]),
                PCF::from(vec![Atomic::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                })]),
            ]
            .into();
            assert_eq!(expected, pcf_set.simplify());
        }
    }

    #[test]
    fn pcf_set_free_vars() {
        {
            let pcf_set = PcfSet::default();
            assert_eq!(Vec::<&Var>::new(), pcf_set.free_vars());
        }
        {
            let pcf_set = PcfSet::from(vec![
                PCF::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                }),
                PCF::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(@c), term!(y)],
                }),
                PCF::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                }),
            ]);
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), pcf_set.free_vars());
        }
    }

    #[test]
    fn pcf_set_transform() {
        {
            let pcf_set: PcfSet = PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(y)],
            })
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
                PcfSet::from(PCF::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z), term!(y)],
                })),
                pcf_set.transform_term(&f)
            );
        }
        {
            let pcf_set: PcfSet = PCF::from(Equals {
                left: term!(f(x)),
                right: term!(y),
            })
            .into();
            let f = |t: &Complex| {
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
            };
            assert_eq!(
                PcfSet::from(PCF::from(Equals {
                    left: term!(z),
                    right: term!(y),
                })),
                pcf_set.transform_term(&f)
            );
        }
    }

    #[test]
    fn pcf_set_signature() {
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

            let pcf_set = PcfSet::from(vec![
                PCF::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }),
                Equals {
                    left: term!(f(x, @c)),
                    right: term!(y),
                }
                .into(),
                Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x, y)), term!(x)],
                }
                .into(),
            ]);
            assert_eq!(sig, pcf_set.signature().unwrap());
        }
        {
            let pcf_set = PcfSet::from(vec![
                PCF::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }),
                Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .into(),
            ]);
            assert!(pcf_set.signature().is_err());
        }
    }

    #[test]
    fn test_gnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_strings!("", gnf(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_strings!("true -> false", gnf(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)", gnf(&formula));
        }
        {
            let formula: FOF = "x = y".parse().unwrap();
            assert_debug_strings!("true -> x = y", gnf(&formula));
        }
        {
            let formula: FOF = "~P(x)".parse().unwrap();
            assert_debug_strings!("P(x) -> false", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x)", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)\ntrue -> Q(x)", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(x)".parse().unwrap();
            assert_debug_strings!("true -> (P(x) | Q(x))", gnf(&formula));
        }
        {
            let formula: FOF = "! x. P(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)", gnf(&formula));
        }
        {
            let formula: FOF = "? x. P(x)".parse().unwrap();
            assert_debug_strings!("true -> P('c#0)", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(x) -> P(y) | Q(y)".parse().unwrap();
            assert_debug_strings!("(P(x) & Q(x)) -> (P(y) | Q(y))", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(x) -> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\nQ(x) -> P(y)\nP(x) -> Q(y)\nQ(x) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "P(x) | Q(x) <=> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "(P(y) & Q(y)) -> (P(x) | Q(x))\nP(x) -> P(y)\nQ(x) -> P(y)\nP(x) -> Q(y)\nQ(x) -> Q(y)",             
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> ?y. Q(x,y))".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x, f#0(x))", gnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> (?y. (Q(y) & R(x, y)) | ?y. (P(y) & S(x, y))))"
                .parse()
                .unwrap();
            assert_debug_strings!(
                "P(x) -> (P(f#1(x)) | Q(f#0(x)))\nP(x) -> (P(f#1(x)) | R(x, f#0(x)))\nP(x) -> (Q(f#0(x)) | S(x, f#1(x)))\nP(x) -> (R(x, f#0(x)) | S(x, f#1(x)))",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "!x, y. ((P(x) & Q(y)) -> (R(x, y) -> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings!("((P(x) & Q(y)) & R(x, y)) -> S(x, y)", gnf(&formula));
        }
        {
            let formula: FOF = "!x, y. ((P(x) & Q(y)) <=> (R(x, y) <=> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings!("true -> ((P(x) | R(x, y)) | S(x, y))\nR(x, y) -> (P(x) | R(x, y))\nS(x, y) -> (P(x) | S(x, y))\n(R(x, y) & S(x, y)) -> P(x)\ntrue -> ((Q(y) | R(x, y)) | S(x, y))\nR(x, y) -> (Q(y) | R(x, y))\nS(x, y) -> (Q(y) | S(x, y))\n(R(x, y) & S(x, y)) -> Q(y)\n((P(x) & Q(y)) & S(x, y)) -> R(x, y)\n((P(x) & Q(y)) & R(x, y)) -> S(x, y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "? x. P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P('c#0) -> Q('c#0)", gnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x`) -> Q(x)", gnf(&formula));
        }
        {
            let formula: FOF = "? x. (P(x) -> Q(x))".parse().unwrap();
            assert_debug_strings!("P('c#0) -> Q('c#0)", gnf(&formula));
        }
        {
            let formula: FOF = "false -> P(x)".parse().unwrap();
            assert_debug_strings!("", gnf(&formula));
        }
    }

    #[test]
    fn gnf_free_vars() {
        {
            let gnf = fof!({'|'} -> {_|_}).gnf();
            assert_eq!(1, gnf.len());
            assert_eq!(Vec::<&Var>::new(), gnf[0].free_vars());
        }
        {
            let gnf = GNF::try_from(fof!({[P(x, @c)] & [Q(y)]} -> {[Q(x)] | [ [Q(y)] & [R()] ]}))
                .unwrap();
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), gnf.free_vars());
        }
    }

    #[test]
    fn gnf_transform() {
        let gnf =
            GNF::try_from(fof!({[P(y, f(x))] & [Q(x)]} -> {[Q(f(x))] | [[R(f(x))] & [R(y)]]}))
                .unwrap();
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
            fof!({[P(y, z)] & [Q(x)]} -> {[Q(z)] | [[R(y)] & [R(z)]]}),
            FOF::from(gnf.transform_term(&f))
        );
    }

    #[test]
    fn gnf_signature() {
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

            let gnf = GNF::try_from(
                fof!({[P(f(x, @c))] & [P(y)]} -> {[P(y)] | [[Q(x, x)] & [(x) = (y)]]}),
            )
            .unwrap();
            assert_eq!(sig, gnf.signature().unwrap());
        }
        {
            let gnf = GNF::try_from(fof!({P(x, x)} -> {P(x)})).unwrap();
            assert!(gnf.signature().is_err());
        }
    }
}
