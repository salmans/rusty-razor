/*! Introduces an abstraction for formulae and various types of connectives as ingredients
for constructing formulae.*/
use super::{
    signature::{FSig, PSig},
    Complex, Error, Pred, Sig, EQ_SYM, V,
};
use crate::transform::TermBased;
use itertools::Itertools;

/// Is the trait of formulae, including first-order formulae.
pub trait Formula {
    fn signature(&self) -> Result<Sig, Error>;
}

/// Represents an atomic formula, obtained by applying a predicate on a list of terms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Atom {
    pub predicate: Pred,
    pub terms: Vec<Complex>,
}

impl TermBased for Atom {
    fn free_vars(&self) -> Vec<&V> {
        self.terms
            .iter()
            .flat_map(|t| t.free_vars())
            .unique()
            .collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            predicate: self.predicate.clone(),
            terms: self.terms.iter().map(f).collect(),
        }
    }
}

fn term_signature(term: &Complex, sig: &mut Sig) -> Result<(), Error> {
    match term {
        Complex::Var { .. } => {}
        Complex::Const { constant } => sig.add_constant(constant.clone()),
        Complex::App { function, terms } => {
            for t in terms {
                term_signature(t, sig)?;
            }

            sig.add_function(FSig {
                symbol: function.clone(),
                arity: terms.len() as u8,
            })?;
        }
    }
    Ok(())
}

impl Formula for Atom {
    fn signature(&self) -> Result<Sig, Error> {
        let mut sig = Sig::new();
        let terms = &self.terms;

        for t in terms {
            term_signature(&t, &mut sig)?;
        }

        sig.add_predicate(PSig {
            symbol: self.predicate.clone(),
            arity: terms.len() as u8,
        })?;
        Ok(sig)
    }
}

/// Represents an equation between two terms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Equals {
    pub left: Complex,
    pub right: Complex,
}

impl TermBased for Equals {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            left: f(&self.left),
            right: f(&self.right),
        }
    }
}

impl Formula for Equals {
    fn signature(&self) -> Result<Sig, Error> {
        let mut sig = Sig::new();
        term_signature(&self.left, &mut sig)?;
        term_signature(&self.right, &mut sig)?;
        sig.add_predicate(PSig {
            symbol: Pred(EQ_SYM.to_string()),
            arity: 2,
        })?;
        Ok(sig)
    }
}

/// Represents the negation of a formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Not<F: Formula> {
    pub formula: F,
}

impl<F: Formula + TermBased> TermBased for Not<F> {
    fn free_vars(&self) -> Vec<&V> {
        self.formula.free_vars()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Not {
            formula: self.formula.transform(f),
        }
    }
}

impl<F: Formula> Formula for Not<F> {
    fn signature(&self) -> Result<Sig, Error> {
        self.formula.signature()
    }
}

/// Represents the conjunction of two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct And<F: Formula> {
    pub left: F,
    pub right: F,
}

impl<F: Formula + TermBased> TermBased for And<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

impl<F: Formula> Formula for And<F> {
    fn signature(&self) -> Result<Sig, Error> {
        self.left.signature()?.merge(self.right.signature()?)
    }
}

/// Represents the disjunction of two formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Or<F: Formula> {
    pub left: F,
    pub right: F,
}

impl<F: Formula + TermBased> TermBased for Or<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

impl<F: Formula> Formula for Or<F> {
    fn signature(&self) -> Result<Sig, Error> {
        self.left.signature()?.merge(self.right.signature()?)
    }
}

/// Represents an implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Implies<F: Formula> {
    pub premise: F,
    pub consequence: F,
}

impl<F: Formula + TermBased> TermBased for Implies<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.premise.free_vars();
        vs.extend(self.consequence.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            premise: self.premise.transform(f),
            consequence: self.consequence.transform(f),
        }
    }
}

impl<F: Formula> Formula for Implies<F> {
    fn signature(&self) -> Result<Sig, Error> {
        self.premise
            .signature()?
            .merge(self.consequence.signature()?)
    }
}

/// Represents a bi-implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Iff<F: Formula> {
    pub left: F,
    pub right: F,
}

impl<F: Formula + TermBased> TermBased for Iff<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

impl<F: Formula> Formula for Iff<F> {
    fn signature(&self) -> Result<Sig, Error> {
        self.left.signature()?.merge(self.right.signature()?)
    }
}

/// Represents an existentially quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Exists<F: Formula> {
    pub variables: Vec<V>,
    pub formula: F,
}

impl<F: Formula + TermBased> TermBased for Exists<F> {
    fn free_vars(&self) -> Vec<&V> {
        self.formula
            .free_vars()
            .into_iter()
            .filter(|v| !self.variables.contains(v))
            .collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            variables: self.variables.clone(),
            formula: self.formula.transform(f),
        }
    }
}

impl<F: Formula> Formula for Exists<F> {
    fn signature(&self) -> Result<Sig, Error> {
        self.formula.signature()
    }
}

/// Represents a universally quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Forall<F: Formula> {
    pub variables: Vec<V>,
    pub formula: F,
}

impl<F: Formula> Formula for Forall<F> {
    fn signature(&self) -> Result<Sig, Error> {
        self.formula.signature()
    }
}

impl<F: Formula + TermBased> TermBased for Forall<F> {
    fn free_vars(&self) -> Vec<&V> {
        self.formula
            .free_vars()
            .into_iter()
            .filter(|v| !self.variables.contains(v))
            .collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            variables: self.variables.clone(),
            formula: self.formula.transform(f),
        }
    }
}

/// Is an atomic formula that wraps an instance of either [`Atom`] or [`Equals`].
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Atomic {
    /// Wraps an atomic formula of type [`Atom`].
    Atom(Atom),

    /// Wraps an (atomic) equation of type [`Equals`].
    Equals(Equals),
}

impl From<Atom> for Atomic {
    fn from(value: Atom) -> Self {
        Self::Atom(value)
    }
}

impl From<Equals> for Atomic {
    fn from(value: Equals) -> Self {
        Self::Equals(value)
    }
}

impl TermBased for Atomic {
    fn free_vars(&self) -> Vec<&V> {
        match self {
            Atomic::Atom(this) => this.free_vars(),
            Atomic::Equals(this) => this.free_vars(),
        }
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            Atomic::Atom(this) => Self::Atom(this.transform(f)),
            Atomic::Equals(this) => Self::Equals(this.transform(f)),
        }
    }
}

impl Formula for Atomic {
    fn signature(&self) -> Result<Sig, Error> {
        match self {
            Atomic::Atom(this) => this.signature(),
            Atomic::Equals(this) => this.signature(),
        }
    }
}

/// A literal is either an [`Atomic`] formula or its negation.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Literal {
    /// Wraps an (positive) [`Atomic`] formula.
    Pos(Atomic),

    /// Wraps the negation of an [`Atomic`] formula.    
    Neg(Atomic),
}

impl Formula for Literal {
    fn signature(&self) -> Result<Sig, Error> {
        match self {
            Literal::Pos(this) => this.signature(),
            Literal::Neg(this) => this.signature(),
        }
    }
}

impl From<Atomic> for Literal {
    fn from(value: Atomic) -> Self {
        Self::Pos(value)
    }
}

impl From<Not<Atomic>> for Literal {
    fn from(value: Not<Atomic>) -> Self {
        Self::Neg(value.formula)
    }
}

impl From<Atom> for Literal {
    fn from(value: Atom) -> Self {
        Self::Pos(value.into())
    }
}

impl From<Not<Atom>> for Literal {
    fn from(value: Not<Atom>) -> Self {
        Self::Neg(value.formula.into())
    }
}

impl From<Equals> for Literal {
    fn from(value: Equals) -> Self {
        Self::Pos(value.into())
    }
}

impl From<Not<Equals>> for Literal {
    fn from(value: Not<Equals>) -> Self {
        Self::Neg(value.formula.into())
    }
}

impl TermBased for Literal {
    fn free_vars(&self) -> Vec<&V> {
        match self {
            Literal::Pos(this) => this.free_vars(),
            Literal::Neg(this) => this.free_vars(),
        }
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            Literal::Pos(this) => this.transform(f).into(),
            Literal::Neg(this) => this.transform(f).into(),
        }
    }
}

/// Defines the quantifier-free portion of standard formula types such as [`PNF`] and [`SNF`].
///
/// [`PNF`]: crate::transform::PNF
/// [`SNF`]: crate::transform::SNF
#[derive(Clone, Debug)]
pub enum QFF {
    /// Is logical top (⊤) or truth.
    Top,

    /// Is logical bottom (⟘) or falsehood.
    Bottom,

    /// Is an atomic formula, wrapping an [`Atom`].
    Atom(Atom),

    /// Is an atomic equality, wrapping an [`Equals`].
    Equals(Equals),

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

impl From<Atom> for QFF {
    fn from(value: Atom) -> Self {
        QFF::Atom(value)
    }
}

impl From<Equals> for QFF {
    fn from(value: Equals) -> Self {
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

impl TermBased for QFF {
    fn free_vars(&self) -> Vec<&V> {
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

impl Formula for QFF {
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
}
