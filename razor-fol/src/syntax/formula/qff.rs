/// Defines a quantifier-free first-order formula of type [`Qff`].
use super::{Error, Sig, Var, *};
use crate::syntax::term::Complex;
use std::fmt;

/// Is the type of the quantifier-free part of formulae types such as [`Pnf`]
/// and [`Snf`].
///
/// [`Pnf`]: crate::transform::Pnf
/// [`Snf`]: crate::transform::Snf
#[derive(PartialEq, Clone)]
pub enum Qff {
    /// Is logical top (⊤) or truth.
    Top,

    /// Is logical bottom (⟘) or falsehood.
    Bottom,

    /// Is an atomic formula, wrapping an [`Atom`].
    Atom(Atom<Complex>),

    /// Is an atomic equality, wrapping an [`Equals`].
    Equals(Equals<Complex>),

    /// Is the negation of a formula, wrapping a [`Not`].
    Not(Box<Not<Qff>>),

    /// Is a conjunction of two formulae, wrapping an [`And`].
    And(Box<And<Qff>>),

    /// Is a disjunction of two formulae, wrapping an [`Or`].
    Or(Box<Or<Qff>>),

    /// Is an implication between two formulae, wrapping an [`Implies`].
    Implies(Box<Implies<Qff>>),

    /// Is an bi-implication between two formulae, wrapping an [`Iff`].    
    Iff(Box<Iff<Qff>>),
}

impl From<Atom<Complex>> for Qff {
    fn from(value: Atom<Complex>) -> Self {
        Qff::Atom(value)
    }
}

impl From<Equals<Complex>> for Qff {
    fn from(value: Equals<Complex>) -> Self {
        Qff::Equals(value)
    }
}

impl From<Not<Qff>> for Qff {
    fn from(value: Not<Qff>) -> Self {
        Qff::Not(Box::new(value))
    }
}

impl From<And<Qff>> for Qff {
    fn from(value: And<Qff>) -> Self {
        Qff::And(Box::new(value))
    }
}

impl From<Or<Qff>> for Qff {
    fn from(value: Or<Qff>) -> Self {
        Qff::Or(Box::new(value))
    }
}

impl From<Implies<Qff>> for Qff {
    fn from(value: Implies<Qff>) -> Self {
        Qff::Implies(Box::new(value))
    }
}

impl From<Iff<Qff>> for Qff {
    fn from(value: Iff<Qff>) -> Self {
        Qff::Iff(Box::new(value))
    }
}

impl Formula for Qff {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        match self {
            Qff::Top => Ok(Sig::new()),
            Qff::Bottom => Ok(Sig::new()),
            Qff::Atom(this) => this.signature(),
            Qff::Equals(this) => this.signature(),
            Qff::Not(this) => this.signature(),
            Qff::And(this) => this.signature(),
            Qff::Or(this) => this.signature(),
            Qff::Implies(this) => this.signature(),
            Qff::Iff(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&Var> {
        match self {
            Self::Top => Vec::new(),
            Self::Bottom => Vec::new(),
            Self::Atom(this) => this.free_vars(),
            Self::Equals(this) => this.free_vars(),
            Self::Not(this) => this.free_vars(),
            Self::And(this) => this.free_vars(),
            Self::Or(this) => this.free_vars(),
            Self::Implies(this) => this.free_vars(),
            Self::Iff(this) => this.free_vars(),
        }
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            Qff::Top | Qff::Bottom => self.clone(),
            Qff::Atom(this) => this.transform_term(f).into(),
            Qff::Equals(this) => this.transform_term(f).into(),
            Qff::Not(this) => this.transform_term(f).into(),
            Qff::And(this) => this.transform_term(f).into(),
            Qff::Or(this) => this.transform_term(f).into(),
            Qff::Implies(this) => this.transform_term(f).into(),
            Qff::Iff(this) => this.transform_term(f).into(),
        }
    }
}

impl FormulaEx for Qff {
    fn precedence(&self) -> u8 {
        match self {
            Qff::Top => PRECEDENCE_ATOM,
            Qff::Bottom => PRECEDENCE_ATOM,
            Qff::Atom(this) => this.precedence(),
            Qff::Equals(this) => this.precedence(),
            Qff::Not(this) => this.precedence(),
            Qff::And(this) => this.precedence(),
            Qff::Or(this) => this.precedence(),
            Qff::Implies(this) => this.precedence(),
            Qff::Iff(this) => this.precedence(),
        }
    }
}

impl fmt::Display for Qff {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Top => write!(f, "⊤"),
            Self::Bottom => write!(f, "⟘"),
            Self::Atom(this) => this.fmt(f),
            Self::Equals(this) => this.fmt(f),
            Self::Not(this) => this.fmt(f),
            Self::And(this) => this.fmt(f),
            Self::Or(this) => this.fmt(f),
            Self::Implies(this) => this.fmt(f),
            Self::Iff(this) => this.fmt(f),
        }
    }
}

impl fmt::Debug for Qff {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Top => write!(f, "⊤"),
            Self::Bottom => write!(f, "⟘"),
            Self::Atom(this) => this.fmt(f),
            Self::Equals(this) => this.fmt(f),
            Self::Not(this) => this.fmt(f),
            Self::And(this) => this.fmt(f),
            Self::Or(this) => this.fmt(f),
            Self::Implies(this) => this.fmt(f),
            Self::Iff(this) => this.fmt(f),
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
            Const, Func, Pred, Sig, EQ_SYM,
        },
        term, v,
    };

    #[test]
    fn atom_to_string() {
        assert_eq!(
            "R()",
            Qff::from(Atom {
                predicate: "R".into(),
                terms: vec![],
            })
            .to_string()
        );
        assert_eq!(
            "R(x, y)",
            Qff::from(Atom {
                predicate: "R".into(),
                terms: vec![term!(x), term!(y)],
            })
            .to_string()
        );
    }

    #[test]
    fn atom_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Qff::from(Atom {
                    predicate: "R".into(),
                    terms: vec![],
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x), term!(y)],
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(y), term!(g(x, z))],
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(z), term!(f(f(f(f(f(f(x)))))))],
                })
                .free_vars()
            );
        }
    }

    #[test]
    fn atom_transform() {
        let formula: Qff = Atom {
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
            Qff::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(z), term!(y)],
            }),
            formula.transform_term(&f)
        );
    }

    #[test]
    fn atom_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: Qff = Atom {
                predicate: "P".into(),
                terms: vec![term!(@c)],
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
            let formula: Qff = Atom {
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
                arity: 3,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("g"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            sig.add_constant(Const::from("d"));
            let formula: Qff = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x, @c)), term!(@d), term!(f(g(x), y))],
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: Qff = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(f(x, y))],
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Qff = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(f(y))],
            }
            .into();
            assert!(formula.signature().is_ok());
        }
    }

    #[test]
    fn equals_to_string() {
        assert_eq!(
            "x = y",
            Qff::from(Equals {
                left: term!(x),
                right: term!(y),
            })
            .to_string()
        );
    }

    #[test]
    fn equals_free_vars() {
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Equals {
                    left: term!(x),
                    right: term!(y),
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Equals {
                    left: term!(x),
                    right: term!(g()),
                })
                .free_vars()
            );
        }
    }

    #[test]
    fn equals_transform() {
        let formula: Qff = Equals {
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
            Qff::from(Equals {
                left: term!(z),
                right: term!(y),
            }),
            formula.transform_term(&f)
        );
    }

    #[test]
    fn equals_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from(EQ_SYM),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: Qff = Equals {
                left: term!(@c),
                right: term!(@c),
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: Qff = Equals {
                left: term!(f(x)),
                right: term!(f(y)),
            }
            .into();
            assert!(formula.signature().is_ok());
        }
        {
            let formula: Qff = Equals {
                left: term!(f(x)),
                right: term!(f(x, y)),
            }
            .into();
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn not_to_string() {
        assert_eq!(
            "¬R(x, y)",
            Qff::from(Not {
                formula: Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x), term!(y)]
                }
                .into()
            })
            .to_string()
        );
    }

    #[test]
    fn not_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Qff::from(Not {
                    formula: Atom {
                        predicate: "R".into(),
                        terms: vec![]
                    }
                    .into()
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Not {
                    formula: Equals {
                        left: term!(x),
                        right: term!(y),
                    }
                    .into()
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Not {
                    formula: Atom {
                        predicate: "R".into(),
                        terms: vec![term!(x), term!(y)]
                    }
                    .into()
                })
                .free_vars()
            );
        }
    }

    #[test]
    fn not_transform() {
        let formula: Qff = Not {
            formula: Atom {
                predicate: "R".into(),
                terms: vec![term!(f(x)), term!(y)],
            }
            .into(),
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
            Qff::from(Not {
                formula: Atom {
                    predicate: "R".into(),
                    terms: vec![term!(z), term!(y)],
                }
                .into()
            }),
            formula.transform_term(&f)
        );
    }

    #[test]
    fn not_signature() {
        let mut sig = Sig::new();
        sig.add_predicate(PredSig {
            symbol: Pred::from("P"),
            arity: 2,
        })
        .unwrap();
        sig.add_function(FuncSig {
            symbol: Func::from("f"),
            arity: 1,
        })
        .unwrap();
        sig.add_constant(Const::from("c"));
        let formula: Qff = Not {
            formula: Atom {
                predicate: "P".into(),
                terms: vec![term!(f(@c)), term!(y)],
            }
            .into(),
        }
        .into();
        assert_eq!(sig, formula.signature().unwrap());
    }

    #[test]
    fn and_to_string() {
        assert_eq!(
            "P() ∧ Q()",
            Qff::from(And {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![]
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![]
                }
                .into(),
            })
            .to_string()
        );
    }

    #[test]
    fn and_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Qff::from(And {
                    left: Atom {
                        predicate: "P".into(),
                        terms: vec![]
                    }
                    .into(),
                    right: Atom {
                        predicate: "Q".into(),
                        terms: vec![]
                    }
                    .into(),
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(And {
                    left: Atom {
                        predicate: "P".into(),
                        terms: vec![term!(z), term!(y)]
                    }
                    .into(),
                    right: Equals {
                        left: term!(x),
                        right: term!(y),
                    }
                    .into()
                })
                .free_vars(),
            );
        }
    }

    #[test]
    fn and_transform() {
        let formula: Qff = And {
            left: Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x))],
            }
            .into(),
            right: Atom {
                predicate: "Q".into(),
                terms: vec![term!(y)],
            }
            .into(),
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
            Qff::from(And {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z)],
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(y)],
                }
                .into(),
            }),
            formula.transform_term(&f)
        );
    }

    #[test]
    fn and_signature() {
        {
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
            let formula: Qff = And {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x)), term!(y)],
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(@c)],
                }
                .into(),
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: Qff = And {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                right: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Qff = And {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
                right: Atom {
                    predicate: "R".into(),
                    terms: vec![term!(f(y))],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_ok());
        }
        {
            let formula: Qff = And {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
                right: Atom {
                    predicate: "R".into(),
                    terms: vec![term!(f(x, y))],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn or_to_string() {
        assert_eq!(
            "P() ∨ Q()",
            Qff::from(Or {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![],
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
            })
            .to_string()
        );
    }

    #[test]
    fn or_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Qff::from(Or {
                    left: Atom {
                        predicate: "P".into(),
                        terms: vec![]
                    }
                    .into(),
                    right: Atom {
                        predicate: "Q".into(),
                        terms: vec![]
                    }
                    .into(),
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Or {
                    left: Atom {
                        predicate: "P".into(),
                        terms: vec![term!(z), term!(y)]
                    }
                    .into(),
                    right: Equals {
                        left: term!(x),
                        right: term!(y),
                    }
                    .into(),
                })
                .free_vars(),
            );
        }
    }

    #[test]
    fn or_transform() {
        let formula: Qff = Or {
            left: Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x))],
            }
            .into(),
            right: Atom {
                predicate: "Q".into(),
                terms: vec![term!(y)],
            }
            .into(),
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
            Qff::from(Or {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z)],
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(y)],
                }
                .into(),
            }),
            formula.transform_term(&f)
        );
    }

    #[test]
    fn or_signature() {
        {
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
            let formula: Qff = Or {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x)), term!(y)],
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(@c)],
                }
                .into(),
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: Qff = Or {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                right: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Qff = Or {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
                right: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x)), term!(y)],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Qff = Or {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
                right: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_ok());
        }
    }

    #[test]
    fn implies_to_string() {
        assert_eq!(
            "P() → Q()",
            Qff::from(Implies {
                premise: Atom {
                    predicate: "P".into(),
                    terms: vec![],
                }
                .into(),
                consequence: Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
            })
            .to_string()
        );
    }

    #[test]
    fn implies_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Qff::from(Implies {
                    premise: Atom {
                        predicate: "P".into(),
                        terms: vec![],
                    }
                    .into(),
                    consequence: Atom {
                        predicate: "Q".into(),
                        terms: vec![],
                    }
                    .into()
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Implies {
                    premise: Atom {
                        predicate: "P".into(),
                        terms: vec![term!(z), term!(y)],
                    }
                    .into(),
                    consequence: Equals {
                        left: term!(x),
                        right: term!(y),
                    }
                    .into()
                })
                .free_vars(),
            );
        }
    }

    #[test]
    fn implies_transform() {
        let formula: Qff = Implies {
            premise: Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x))],
            }
            .into(),
            consequence: Atom {
                predicate: "Q".into(),
                terms: vec![term!(y)],
            }
            .into(),
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
            Qff::from(Implies {
                premise: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z)],
                }
                .into(),
                consequence: Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(y)],
                }
                .into(),
            }),
            formula.transform_term(&f)
        );
    }

    #[test]
    fn implies_signature() {
        {
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
            let formula: Qff = Implies {
                premise: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x)), term!(y)],
                }
                .into(),
                consequence: Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(@c)],
                }
                .into(),
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: Qff = Implies {
                premise: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                consequence: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Qff = Implies {
                premise: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
                consequence: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x, y))],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Qff = Implies {
                premise: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
                consequence: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_ok());
        }
    }

    #[test]
    fn iff_to_string() {
        assert_eq!(
            "P() ⇔ Q()",
            Qff::from(Iff {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![],
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
            })
            .to_string()
        );
    }

    #[test]
    fn iff_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Qff::from(Iff {
                    left: Atom {
                        predicate: "P".into(),
                        terms: vec![],
                    }
                    .into(),
                    right: Atom {
                        predicate: "Q".into(),
                        terms: vec![],
                    }
                    .into(),
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Qff::from(Iff {
                    left: Atom {
                        predicate: "P".into(),
                        terms: vec![term!(z), term!(y)],
                    }
                    .into(),
                    right: Equals {
                        left: term!(x),
                        right: term!(y),
                    }
                    .into(),
                })
                .free_vars(),
            );
        }
    }

    #[test]
    fn iff_transform() {
        let formula: Qff = Iff {
            left: Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x))],
            }
            .into(),
            right: Atom {
                predicate: "Q".into(),
                terms: vec![term!(y)],
            }
            .into(),
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
            Qff::from(Iff {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z)],
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(y)],
                }
                .into(),
            }),
            formula.transform_term(&f)
        );
    }

    #[test]
    fn iff_signature() {
        {
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
            let formula: Qff = Iff {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x)), term!(y)],
                }
                .into(),
                right: Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(@c)],
                }
                .into(),
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: Qff = Iff {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                right: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Qff = Iff {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
                right: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x, y))],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_err());
        }
        {
            let formula: Qff = Iff {
                left: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
                right: Atom {
                    predicate: "P".into(),
                    terms: vec![term!(f(x))],
                }
                .into(),
            }
            .into();
            assert!(formula.signature().is_ok());
        }
    }
}
