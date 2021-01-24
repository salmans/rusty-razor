/*! Defines formulae in Geometric Normal Form (GNF) and implements an algorithm for
converting a [`CNF`] to a [`GNF`].

[`CNF`]: crate::transform::CNF
*/
use super::{ToCNF, CNF};
use crate::syntax::{
    formula::{
        clause::{Clause, Literal},
        *,
    },
    term::Complex,
    Error, Sig, Theory, Var, FOF,
};
use itertools::Itertools;
use std::{collections::BTreeSet, ops::Deref};

// A positive literal is simply an atomic formula.
type PosLiteral = Atomic<Complex>;

/// A Positive Conjunctive Formula (PCF) represents a collection of [`Atomic`]s, interpreted
/// as a conjunction of positive literals. PCFs are the building blocks of [`GNF`]s.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct PCF(BTreeSet<PosLiteral>);

impl PCF {
    /// Returns the atomic formulae of the receiver clause.
    #[inline(always)]
    pub fn atomics(&self) -> &BTreeSet<PosLiteral> {
        &self.0
    }

    /// Consumes the receiver and returns its underlying list of atomic formulae.
    pub fn into_atomics(self) -> BTreeSet<PosLiteral> {
        self.0
    }

    /// Returns a new clause, resulting from joining the atomic formulae of the
    /// receiver and `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().into()
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
        vec![value].into_iter().into()
    }
}

impl From<Atom<Complex>> for PCF {
    fn from(value: Atom<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().into()
    }
}

impl From<Equals<Complex>> for PCF {
    fn from(value: Equals<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().into()
    }
}

impl<I> From<I> for PCF
where
    I: IntoIterator<Item = PosLiteral>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Default for PCF {
    fn default() -> Self {
        Vec::<PosLiteral>::new().into()
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

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        self.iter().map(|lit| lit.transform(f)).into()
    }
}

impl From<PCF> for FOF {
    fn from(value: PCF) -> Self {
        value
            .into_atomics()
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

/// Is a set of [`PCF`]s in the head of a [`GNF`], interpreted as a disjunction of
/// PCFs where each PCF is a conjunction of positive literals.
#[derive(PartialEq, Clone, Debug)]
pub struct PCFSet(BTreeSet<PCF>);

impl PCFSet {
    /// Returns the clauses of the receiver.
    #[inline(always)]
    pub fn clauses(&self) -> &BTreeSet<PCF> {
        &self.0
    }

    /// Consumes the receiver and returns its underlying set of clauses.
    pub fn into_clauses(self) -> BTreeSet<PCF> {
        self.0
    }

    /// Returns a new positive clause set, containing clauses obtained by pairwise unioning
    /// of the clauses in the receiver and `other`.
    pub fn cross_union(&self, other: &Self) -> Self {
        self.iter()
            .flat_map(|h1| other.iter().map(move |h2| h1.union(&h2)))
            .into()
    }

    /// Returns a new pcf set obtained by removing pcfs that are proper supersets of
    /// some other pcfs in the receiver.
    pub fn simplify(&self) -> Self {
        self.iter()
            .filter(|c1| !self.iter().any(|c2| *c1 != c2 && c2.is_subset(c1)))
            .cloned()
            .into()
    }
}

impl From<PCF> for PCFSet {
    fn from(value: PCF) -> Self {
        vec![value].into_iter().into()
    }
}

impl<I> From<I> for PCFSet
where
    I: IntoIterator<Item = PCF>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Deref for PCFSet {
    type Target = BTreeSet<PCF>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Default for PCFSet {
    fn default() -> Self {
        Vec::<PCF>::new().into()
    }
}

impl Formula for PCFSet {
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

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        self.iter().map(|lit| lit.transform(f)).into()
    }
}

impl From<PCFSet> for FOF {
    fn from(value: PCFSet) -> Self {
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

impl From<&PCFSet> for FOF {
    fn from(value: &PCFSet) -> Self {
        value.clone().into()
    }
}

/// Represents a formula in Geometric Normal Form (GNF), consisting of a [`PCF`] in the body
/// (premise) and a [`PCFSet`] in the head (consequence).
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
    head: PCFSet,
}

impl GNF {
    /// Returns the body of the receiver GNF.
    #[inline(always)]
    pub fn body(&self) -> &PCF {
        &self.body
    }

    /// Returns the head of the receiver GNF.
    #[inline(always)]
    pub fn head(&self) -> &PCFSet {
        &self.head
    }

    /// Consumes the receiver and returns its body and head.
    pub fn into_body_and_head(self) -> (PCF, PCFSet) {
        (self.body, self.head)
    }
}

impl From<(PCF, PCFSet)> for GNF {
    fn from(value: (PCF, PCFSet)) -> Self {
        let (body, head) = value;
        Self { body, head }
    }
}

pub trait ToGNF: Formula {
    /// Transforms the receiver [`Formula`] to a list of formulae in Geometric Normal
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

impl ToGNF for CNF {
    fn gnf(&self) -> Vec<GNF> {
        let gnfs = self.iter().map(gnf).collect();
        contract(gnfs)
    }
}

impl<T: ToCNF> ToGNF for T {
    fn gnf(&self) -> Vec<GNF> {
        self.cnf().gnf()
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

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            body: self.body.transform(f),
            head: self.head.transform(f),
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

// Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
fn gnf(clause: &Clause<Complex>) -> GNF {
    let mut head: Vec<PCF> = Vec::new();
    let mut body: Vec<Atomic<_>> = Vec::new();
    clause.iter().for_each(|lit| match lit {
        Literal::Pos(this) => head.push(this.clone().into()),
        Literal::Neg(this) => body.push(this.clone()),
    });

    let body = PCF::from(body);
    let head = PCFSet::from(head);
    (body, head).into()
}

impl<T: ToGNF> Theory<T> {
    /// Transforms the given theory to a *geometric theory* of formulae in
    /// Geometric Normal Form ([`GNF`]).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{FOF, Theory};
    ///
    /// let theory: Theory<FOF> = r#"
    ///     not P(x) or Q(x);
    ///     Q(x) -> exists y. R(x, y);
    /// "#.parse().unwrap();
    /// assert_eq!(r#"P(x) → Q(x)
    /// Q(x) → R(x, f#0(x))"#, theory.gnf().to_string());
    /// ```
    pub fn gnf(&self) -> Theory<GNF> {
        use std::convert::TryFrom;

        let formulae = self.formulae().iter().flat_map(|f| f.gnf()).collect_vec();

        // Assuming that the conversion does not change the signature of the theory,
        // so it's safe to unwrap:
        Theory::try_from(contract(formulae)).unwrap()
    }
}

// a helper to merge sequents with syntactically identical bodies
fn contract(formulae: Vec<GNF>) -> Vec<GNF> {
    formulae
        .into_iter()
        .sorted_by(|first, second| first.body().cmp(second.body()))
        .into_iter()
        .coalesce(|first, second| {
            // merge the ones with the same body:
            let body_vars = first.body().free_vars();
            let head_vars = first.head().free_vars();
            // contract sequents with no free variables that show up only in head:
            if head_vars
                .iter()
                .all(|hv| body_vars.iter().any(|bv| bv == hv))
            {
                let body_vars = second.body().free_vars();
                let head_vars = second.head().free_vars();
                if head_vars
                    .iter()
                    .all(|hv| body_vars.iter().any(|bv| bv == hv))
                {
                    if first.body() == second.body() {
                        Ok(GNF::from((
                            first.body().clone(),
                            first.head().cross_union(second.head()),
                        )))
                    } else {
                        Err((first, second))
                    }
                } else {
                    Err((second, first))
                }
            } else {
                Err((first, second))
            }
        })
        .into_iter()
        .map(|g| (g.body().clone(), g.head().simplify()).into())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assert_debug_strings, assert_eq_sorted_vecs, fof,
        syntax::{
            signature::{FuncSig, PredSig},
            Sig, Theory, EQ_SYM,
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
                pcf.transform(&f)
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
                pcf.transform(&f)
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
            let first = PCFSet::default();
            let second = PCFSet::default();
            assert_eq!(PCFSet::default(), first.cross_union(&second));
        }
        {
            let first = PCFSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            let second = PCFSet::default();
            assert_eq!(PCFSet::default(), first.cross_union(&second));
            assert_eq!(PCFSet::default(), second.cross_union(&first));
        }
        {
            let first = PCFSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            let second = PCFSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            assert_eq!(first, first.cross_union(&second));
        }
        {
            let first = PCFSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            let second = PCFSet::from(vec![PCF::from(Atom {
                predicate: "Q".into(),
                terms: vec![],
            })]);
            let expected = PCFSet::from(vec![PCF::from(vec![
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
            let first = PCFSet::from(vec![PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            })]);
            let second = PCFSet::from(vec![PCF::from(vec![
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
            let expected = PCFSet::from(vec![PCF::from(vec![
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
            let first = PCFSet::from(vec![
                PCF::from(Atomic::from(Atom {
                    predicate: "P".into(),
                    terms: vec![],
                })),
                PCF::from(Atomic::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                })),
            ]);
            let second = PCFSet::from(vec![
                PCF::from(Atomic::from(Atom {
                    predicate: "R".into(),
                    terms: vec![],
                })),
                PCF::from(Atomic::from(Atom {
                    predicate: "S".into(),
                    terms: vec![],
                })),
            ]);
            let expected = PCFSet::from(vec![
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
            let pcf_set = PCFSet::default();
            assert_eq!(pcf_set, pcf_set.simplify());
        }
        {
            let pcf_set: PCFSet = vec![PCF::from(vec![Atomic::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(x)],
            })])]
            .into();
            assert_eq!(pcf_set, pcf_set.simplify());
        }
        {
            let pcf_set: PCFSet = vec![
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
            let expected: PCFSet = vec![
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
            let pcf_set = PCFSet::default();
            assert_eq!(Vec::<&Var>::new(), pcf_set.free_vars());
        }
        {
            let pcf_set = PCFSet::from(vec![
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
            let pcf_set: PCFSet = PCF::from(Atom {
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
                PCFSet::from(PCF::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z), term!(y)],
                })),
                pcf_set.transform(&f)
            );
        }
        {
            let pcf_set: PCFSet = PCF::from(Equals {
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
                PCFSet::from(PCF::from(Equals {
                    left: term!(z),
                    right: term!(y),
                })),
                pcf_set.transform(&f)
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

            let pcf_set = PCFSet::from(vec![
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
            let pcf_set = PCFSet::from(vec![
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
                "P(x) -> P(y)\nP(x) -> Q(y)\nQ(x) -> P(y)\nQ(x) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "P(x) | Q(x) <=> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\nP(x) -> Q(y)\n(P(y) & Q(y)) -> (P(x) | Q(x))\nQ(x) -> P(y)\nQ(x) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> ?y. Q(x,y))".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x, f#0(x))", gnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> (?y. (Q(y) & R(x, y)) | ?y. (P(y) & S(x, y)))))"
                .parse()
                .unwrap();
            assert_debug_strings!(
                "P(x) -> ((P(f#1(x)) & S(x, f#1(x))) | (Q(f#0(x)) & R(x, f#0(x))))",
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
            assert_debug_strings!("true -> ((P(x) | R(x, y)) | S(x, y))\ntrue -> ((Q(y) | R(x, y)) | S(x, y))\n((P(x) & Q(y)) & R(x, y)) -> S(x, y)\n((P(x) & Q(y)) & S(x, y)) -> R(x, y)\nR(x, y) -> ((P(x) & Q(y)) | R(x, y))\n(R(x, y) & S(x, y)) -> (P(x) & Q(y))\nS(x, y) -> ((P(x) & Q(y)) | S(x, y))",
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
            // Only the heads of range-restricted formula get contracted:
            let gnf = fof!({[P(x, @c)] & [Q(y)]} -> {[Q(x)] | [ [Q(y)] & [R()] ]}).gnf();
            assert_eq!(1, gnf.len());
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), gnf[0].free_vars());
        }
    }

    #[test]
    fn gnf_transform() {
        let gnf = fof!({[P(y, f(x))] & [Q(x)]} -> {[Q(f(x))] | [[R(f(x))] & [R(y)]]}).gnf();
        assert_eq!(1, gnf.len());
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
            FOF::from(gnf[0].transform(&f))
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

            let gnf = fof!({[P(f(x, @c))] & [P(y)]} -> {[P(y)] | [[Q(x, x)] & [(x) = (y)]]}).gnf();
            assert_eq!(1, gnf.len());
            assert_eq!(sig, gnf[0].signature().unwrap());
        }
        {
            let gnf = fof!({P(x, x)} -> {P(x)}).gnf();
            assert_eq!(1, gnf.len());
            assert!(gnf[0].signature().is_err());
        }
    }

    #[test]
    fn test_gnf_theory() {
        // mostly testing if contraction works properly:
        {
            let theory: Theory<FOF> = "P('a); P('b);".parse().unwrap();
            assert_eq!("⊤ → (P(\'a) ∧ P(\'b))", theory.gnf().to_string());
        }
        {
            let theory: Theory<FOF> = "P('a); P(x);".parse().unwrap();
            assert_eq!("⊤ → P(x)\n⊤ → P(\'a)", theory.gnf().to_string());
        }
        {
            let theory: Theory<FOF> = "P('a); P(x); P('b);".parse().unwrap();
            assert_eq!("⊤ → P(x)\n⊤ → (P(\'a) ∧ P(\'b))", theory.gnf().to_string(),);
        }
        {
            let theory: Theory<FOF> = "(T() and V()) or (U() and V());".parse().unwrap();
            assert_eq!("⊤ → ((T() ∧ V()) ∨ (U() ∧ V()))", theory.gnf().to_string());
        }
    }
}
