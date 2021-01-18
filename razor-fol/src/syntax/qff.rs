/// Defines a quantifier-free first-order formula of type [`QFF`].
use super::{formula::*, term::Complex, Error, Sig, Var};
use std::fmt;

/// Is the type of quantifier-free sub-formula of formulae types such as [`PNF`]
/// and [`SNF`].
///
/// [`PNF`]: crate::transform::PNF
/// [`SNF`]: crate::transform::SNF
#[derive(Clone)]
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
