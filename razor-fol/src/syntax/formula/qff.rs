/// Defines a quantifier-free first-order formula of type [`QFF`].
use super::{Error, Sig, Var, *};
use crate::syntax::term::Complex;
use std::fmt;

/// Is the type of quantifier-free sub-formula of formulae types such as [`PNF`]
/// and [`SNF`].
///
/// [`PNF`]: crate::transform::PNF
/// [`SNF`]: crate::transform::SNF
#[derive(PartialEq, Clone)]
pub enum QFF {
    /// Is logical top (⊤) or truth.
    Top,

    /// Is logical bottom (⟘) or falsehood.
    Bottom,

    /// Is an atomic formula, wrapping an [`Atom`].
    Atom(Atom<Complex>),

    /// Is an atomic equality, wrapping an [`Equals`].
    Equals(Equals<Complex>),

    /// Is the negation of a formula, wrapping a [`Not`].
    Not(Box<Not<QFF>>),

    /// Is a conjunction of two formulae, wrapping an [`And`].
    And(Box<And<QFF>>),

    /// Is a disjunction of two formulae, wrapping an [`Or`].
    Or(Box<Or<QFF>>),

    /// Is an implication between two formulae, wrapping an [`Implies`].
    Implies(Box<Implies<QFF>>),

    /// Is an bi-implication between two formulae, wrapping an [`Iff`].    
    Iff(Box<Iff<QFF>>),
}

impl From<Atom<Complex>> for QFF {
    fn from(value: Atom<Complex>) -> Self {
        QFF::Atom(value)
    }
}

impl From<Equals<Complex>> for QFF {
    fn from(value: Equals<Complex>) -> Self {
        QFF::Equals(value)
    }
}

impl From<Not<QFF>> for QFF {
    fn from(value: Not<QFF>) -> Self {
        QFF::Not(Box::new(value))
    }
}

impl From<And<QFF>> for QFF {
    fn from(value: And<QFF>) -> Self {
        QFF::And(Box::new(value))
    }
}

impl From<Or<QFF>> for QFF {
    fn from(value: Or<QFF>) -> Self {
        QFF::Or(Box::new(value))
    }
}

impl From<Implies<QFF>> for QFF {
    fn from(value: Implies<QFF>) -> Self {
        QFF::Implies(Box::new(value))
    }
}

impl From<Iff<QFF>> for QFF {
    fn from(value: Iff<QFF>) -> Self {
        QFF::Iff(Box::new(value))
    }
}

impl Formula for QFF {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        match self {
            QFF::Top => Ok(Sig::new()),
            QFF::Bottom => Ok(Sig::new()),
            QFF::Atom(this) => this.signature(),
            QFF::Equals(this) => this.signature(),
            QFF::Not(this) => this.signature(),
            QFF::And(this) => this.signature(),
            QFF::Or(this) => this.signature(),
            QFF::Implies(this) => this.signature(),
            QFF::Iff(this) => this.signature(),
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

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            QFF::Top | QFF::Bottom => self.clone(),
            QFF::Atom(this) => this.transform(f).into(),
            QFF::Equals(this) => this.transform(f).into(),
            QFF::Not(this) => this.transform(f).into(),
            QFF::And(this) => this.transform(f).into(),
            QFF::Or(this) => this.transform(f).into(),
            QFF::Implies(this) => this.transform(f).into(),
            QFF::Iff(this) => this.transform(f).into(),
        }
    }
}

impl FormulaEx for QFF {
    fn precedence(&self) -> u8 {
        match self {
            QFF::Top => PRECEDENCE_ATOM,
            QFF::Bottom => PRECEDENCE_ATOM,
            QFF::Atom(this) => this.precedence(),
            QFF::Equals(this) => this.precedence(),
            QFF::Not(this) => this.precedence(),
            QFF::And(this) => this.precedence(),
            QFF::Or(this) => this.precedence(),
            QFF::Implies(this) => this.precedence(),
            QFF::Iff(this) => this.precedence(),
        }
    }
}

impl fmt::Display for QFF {
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

impl fmt::Debug for QFF {
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
            signature::{FSig, PSig},
            Const, Func, Pred, Sig, EQ_SYM,
        },
        term, v,
    };

    #[test]
    fn atom_to_string() {
        assert_eq!(
            "R()",
            QFF::from(Atom {
                predicate: "R".into(),
                terms: vec![],
            })
            .to_string()
        );
        assert_eq!(
            "R(x, y)",
            QFF::from(Atom {
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
                QFF::from(Atom {
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
                QFF::from(Atom {
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
                QFF::from(Atom {
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
                QFF::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(z), term!(f(f(f(f(f(f(x)))))))],
                })
                .free_vars()
            );
        }
    }

    #[test]
    fn atom_transform() {
        let formula: QFF = Atom {
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
            QFF::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(z), term!(y)],
            }),
            formula.transform(&f)
        );
    }

    #[test]
    fn atom_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: QFF = Atom {
                predicate: "P".into(),
                terms: vec![term!(@c)],
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: Func::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: QFF = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x, @c))],
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 3,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: Func::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: Func::from("g"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            sig.add_constant(Const::from("d"));
            let formula: QFF = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x, @c)), term!(@d), term!(f(g(x), y))],
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: QFF = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(f(x, y))],
            }
            .into();
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn equals_to_string() {
        assert_eq!(
            "x = y",
            QFF::from(Equals {
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
                QFF::from(Equals {
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
                QFF::from(Equals {
                    left: term!(x),
                    right: term!(g()),
                })
                .free_vars()
            );
        }
    }

    #[test]
    fn equals_transform() {
        let formula: QFF = Equals {
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
            QFF::from(Equals {
                left: term!(z),
                right: term!(y),
            }),
            formula.transform(&f)
        );
    }

    #[test]
    fn equals_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from(EQ_SYM),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: QFF = Equals {
                left: term!(@c),
                right: term!(@c),
            }
            .into();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula: QFF = Equals {
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
            QFF::from(Not {
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
                QFF::from(Not {
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
                QFF::from(Not {
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
                QFF::from(Not {
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
        let formula: QFF = Not {
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
            QFF::from(Not {
                formula: Atom {
                    predicate: "R".into(),
                    terms: vec![term!(z), term!(y)],
                }
                .into()
            }),
            formula.transform(&f)
        );
    }

    #[test]
    fn not_signature() {
        let mut sig = Sig::new();
        sig.add_predicate(PSig {
            symbol: Pred::from("P"),
            arity: 2,
        })
        .unwrap();
        sig.add_function(FSig {
            symbol: Func::from("f"),
            arity: 1,
        })
        .unwrap();
        sig.add_constant(Const::from("c"));
        let formula: QFF = Not {
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
            QFF::from(And {
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
                QFF::from(And {
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
                QFF::from(And {
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
        let formula: QFF = And {
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
            QFF::from(And {
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
            formula.transform(&f)
        );
    }

    #[test]
    fn and_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: QFF = And {
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
            let formula: QFF = And {
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
            let formula: QFF = And {
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
            QFF::from(Or {
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
                QFF::from(Or {
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
                QFF::from(Or {
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
        let formula: QFF = Or {
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
            QFF::from(Or {
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
            formula.transform(&f)
        );
    }

    #[test]
    fn or_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: QFF = Or {
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
            let formula: QFF = Or {
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
            let formula: QFF = Or {
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
    }

    #[test]
    fn implies_to_string() {
        assert_eq!(
            "P() → Q()",
            QFF::from(Implies {
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
                QFF::from(Implies {
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
                QFF::from(Implies {
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
        let formula: QFF = Implies {
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
            QFF::from(Implies {
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
            formula.transform(&f)
        );
    }

    #[test]
    fn implies_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: QFF = Implies {
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
            let formula: QFF = Implies {
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
            let formula: QFF = Implies {
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
    }

    #[test]
    fn iff_to_string() {
        assert_eq!(
            "P() ⇔ Q()",
            QFF::from(Iff {
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
                QFF::from(Iff {
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
                QFF::from(Iff {
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
        let formula: QFF = Iff {
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
            QFF::from(Iff {
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
            formula.transform(&f)
        );
    }

    #[test]
    fn iff_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula: QFF = Iff {
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
            let formula: QFF = Iff {
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
            let formula: QFF = Iff {
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
    }
}
