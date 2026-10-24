//! Defines literals: atomic formulae and their negations.
use super::{Atom, Atomic, Equals, Formula, FormulaEx, Not};
use crate::syntax::{Error, Sig, Term, Var};

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
            let expected = [v!(x), v!(y)];
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
            let expected = [v!(x), v!(y)];
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
            let expected = [v!(x), v!(y)];
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
            let expected = [v!(x), v!(y)];
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
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
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
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
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
}
