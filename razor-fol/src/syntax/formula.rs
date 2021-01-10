/*! Introduces an abstraction for formulae and various generic types as building blocks
for various formula types.*/
pub mod clause;

use super::{
    signature::PSig,
    term::{Renaming, Substitution},
    Error, Pred, Sig, Term, Var, EQ_SYM,
};
use itertools::Itertools;
use std::{fmt, hash::Hash};

/// Is the trait of formulae, including first-order formulae.
pub trait Formula {
    /// Is the type of [`Term`]s in this type of formula.
    type Term: Term;

    /// Returns the signature on which the formula is defined. It fails if there are
    /// the underlying signature is inconsistent.
    fn signature(&self) -> Result<Sig, Error>;

    /// Returns a list of free variable symbols in the receiver.
    ///
    /// **Note**: In the list of variables, each variable symbol appears only once
    /// even if it is present at multiple positions of the receiver.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{Var, FOF};
    /// # use itertools::Itertools;
    /// use razor_fol::syntax::Formula;
    ///
    /// // `x`, `y` and `z` are variable symbols:
    /// let x = Var::from("x");
    /// let y = Var::from("y");
    /// let z = Var::from("z");
    ///
    /// // (P(x) ∧ Q(x, f(g(x), y))) ∨ ('c = g(z))
    /// let formula: FOF = "(P(x) & Q(x, f(g(x), y))) |  'c = g(z)".parse().unwrap();
    /// assert_eq!(vec![&x, &y, &z].iter().sorted(), formula.free_vars().iter().sorted());
    ///
    /// // ∀ x. P(x, y)
    /// let formula: FOF = "forall x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars());
    ///
    /// // ∃ x. P(x, y)
    /// let formula: FOF = "exists x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars());
    /// ```    
    fn free_vars(&self) -> Vec<&Var>;

    /// Applies a transformation function `f` recursively on the terms of the receiver.
    ///
    /// [`Term`]: crate::syntax::Term
    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self;

    /// Applies a [`Renaming`] recursively on the variable subterms of the receiver.
    fn rename_vars(&self, renaming: &impl Renaming) -> Self
    where
        Self: Sized,
    {
        self.transform(&|t: &Self::Term| t.rename_vars(renaming))
    }

    /// Applies a [`Substitution`] recursively on the variable terms of the receiver.
    fn substitute(&self, sub: &impl Substitution<Self::Term>) -> Self
    where
        Self: Sized,
    {
        self.transform(&|t: &Self::Term| t.substitute(sub))
    }
}

/// Represents an atomic formula, obtained by applying a predicate on a list of terms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Atom<T: Term> {
    /// Is the predicate that is applied on terms of this atomic formula.
    pub predicate: Pred,

    /// Is the list of terms on which the predicate is applied.
    pub terms: Vec<T>,
}

impl<T: Term> Formula for Atom<T> {
    type Term = T;

    fn signature(&self) -> Result<Sig, Error> {
        let mut sig = Sig::new();
        let terms = &self.terms;

        for t in terms {
            sig = sig.merge(t.signature()?)?;
        }

        sig.add_predicate(PSig {
            symbol: self.predicate.clone(),
            arity: terms.len() as u8,
        })?;
        Ok(sig)
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.terms.iter().flat_map(|t| t.vars()).unique().collect()
    }

    fn transform(&self, f: &impl Fn(&T) -> T) -> Self {
        Self {
            predicate: self.predicate.clone(),
            terms: self.terms.iter().map(f).collect(),
        }
    }
}

impl<T: Term + fmt::Display> fmt::Display for Atom<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ts = self.terms.iter().map(|t| t.to_string()).collect_vec();
        write!(f, "{}({})", self.predicate.to_string(), ts.join(", "))
    }
}

/// Represents an equation between two terms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Equals<T: Term> {
    /// Is the term on left of this equation.
    pub left: T,

    /// Is the term on right of this equation.
    pub right: T,
}

impl<T: Term> Formula for Equals<T> {
    type Term = T;

    fn signature(&self) -> Result<Sig, Error> {
        let mut sig = Sig::new();
        sig = sig.merge(self.left.signature()?)?;
        sig = sig.merge(self.right.signature()?)?;
        sig.add_predicate(PSig {
            symbol: Pred::from(EQ_SYM),
            arity: 2,
        })?;
        Ok(sig)
    }

    fn free_vars(&self) -> Vec<&Var> {
        let mut vs = self.left.vars();
        vs.extend(self.right.vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&T) -> T) -> Self {
        Self {
            left: f(&self.left),
            right: f(&self.right),
        }
    }
}

impl<T: Term + fmt::Display> fmt::Display for Equals<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.left, self.right)
    }
}

/// Represents the negation of a formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Not<F: Formula> {
    /// Is the negated formula.
    pub formula: F,
}

impl<F: Formula> Formula for Not<F> {
    type Term = F::Term;

    fn signature(&self) -> Result<Sig, Error> {
        self.formula.signature()
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.formula.free_vars()
    }

    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Not {
            formula: self.formula.transform(f),
        }
    }
}

impl<F: Formula + fmt::Display> fmt::Display for Not<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "¬{}", self.formula)
    }
}

/// Represents the conjunction of two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct And<F: Formula> {
    /// Is the formula on left of this conjunction.
    pub left: F,

    /// Is the formula on right of this conjunction.
    pub right: F,
}

impl<F: Formula> Formula for And<F> {
    type Term = F::Term;

    fn signature(&self) -> Result<Sig, Error> {
        self.left.signature()?.merge(self.right.signature()?)
    }

    fn free_vars(&self) -> Vec<&Var> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

impl<F: Formula + fmt::Display> fmt::Display for And<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ∧ {}", self.left, self.right)
    }
}

/// Represents the disjunction of two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Or<F: Formula> {
    /// Is the formula on left of this disjunction.
    pub left: F,

    /// Is the formula on right of this disjunction.
    pub right: F,
}

impl<F: Formula> Formula for Or<F> {
    type Term = F::Term;

    fn signature(&self) -> Result<Sig, Error> {
        self.left.signature()?.merge(self.right.signature()?)
    }

    fn free_vars(&self) -> Vec<&Var> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

impl<F: Formula + fmt::Display> fmt::Display for Or<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ∨ {}", self.left, self.right)
    }
}

/// Represents an implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Implies<F: Formula> {
    /// Is the premise (formula) of this implication.
    pub premise: F,

    /// Is the consequence (formula) of this implication.
    pub consequence: F,
}

impl<F: Formula> Formula for Implies<F> {
    type Term = F::Term;

    fn signature(&self) -> Result<Sig, Error> {
        self.premise
            .signature()?
            .merge(self.consequence.signature()?)
    }

    fn free_vars(&self) -> Vec<&Var> {
        let mut vs = self.premise.free_vars();
        vs.extend(self.consequence.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Self {
            premise: self.premise.transform(f),
            consequence: self.consequence.transform(f),
        }
    }
}

impl<F: Formula + fmt::Display> fmt::Display for Implies<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} → {}", self.premise, self.consequence)
    }
}

/// Represents a bi-implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Iff<F: Formula> {
    /// Is the formula on left of this bi-implication.
    pub left: F,

    /// Is the formula on right of this bi-implication.
    pub right: F,
}

impl<F: Formula> Formula for Iff<F> {
    type Term = F::Term;

    fn signature(&self) -> Result<Sig, Error> {
        self.left.signature()?.merge(self.right.signature()?)
    }

    fn free_vars(&self) -> Vec<&Var> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

impl<F: Formula + fmt::Display> fmt::Display for Iff<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ⇔ {}", self.left, self.right)
    }
}

/// Represents an existentially quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Exists<F: Formula> {
    /// Is the list of variables bound by this quantifier.
    pub variables: Vec<Var>,

    /// Is the scope (formula) of the quantified formula.
    pub formula: F,
}

impl<F: Formula> Formula for Exists<F> {
    type Term = F::Term;

    fn signature(&self) -> Result<Sig, Error> {
        self.formula.signature()
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.formula
            .free_vars()
            .into_iter()
            .filter(|v| !self.variables.contains(v))
            .collect()
    }

    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Self {
            variables: self.variables.clone(),
            formula: self.formula.transform(f),
        }
    }
}

impl<F: Formula + fmt::Display> fmt::Display for Exists<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vs = self.variables.iter().map(|t| t.to_string()).collect_vec();
        write!(f, "∃ {}. {}", vs.join(", "), self.formula)
    }
}

/// Represents a universally quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Forall<F: Formula> {
    /// Is the list of variables bound by this quantifier.
    pub variables: Vec<Var>,

    /// Is the scope (formula) of the quantified formula.
    pub formula: F,
}

impl<F: Formula> Formula for Forall<F> {
    type Term = F::Term;

    fn signature(&self) -> Result<Sig, Error> {
        self.formula.signature()
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.formula
            .free_vars()
            .into_iter()
            .filter(|v| !self.variables.contains(v))
            .collect()
    }

    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Self {
            variables: self.variables.clone(),
            formula: self.formula.transform(f),
        }
    }
}

impl<F: Formula + fmt::Display> fmt::Display for Forall<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vs: Vec<_> = self.variables.iter().map(|t| t.to_string()).collect();
        write!(f, "∀ {}. {}", vs.join(", "), self.formula)
    }
}

/// Is an atomic formula that wraps an instance of either [`Atom`] or [`Equals`].
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Atomic<T: Term> {
    /// Wraps an atomic formula of type [`Atom`].
    Atom(Atom<T>),

    /// Wraps an (atomic) equation of type [`Equals`].
    Equals(Equals<T>),
}

impl<T: Term> From<Atom<T>> for Atomic<T> {
    fn from(value: Atom<T>) -> Self {
        Self::Atom(value)
    }
}

impl<T: Term> From<Equals<T>> for Atomic<T> {
    fn from(value: Equals<T>) -> Self {
        Self::Equals(value)
    }
}

impl<T: Term> Formula for Atomic<T> {
    type Term = T;

    fn signature(&self) -> Result<Sig, Error> {
        match self {
            Atomic::Atom(this) => this.signature(),
            Atomic::Equals(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&Var> {
        match self {
            Atomic::Atom(this) => this.free_vars(),
            Atomic::Equals(this) => this.free_vars(),
        }
    }

    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        match self {
            Atomic::Atom(this) => Self::Atom(this.transform(f)),
            Atomic::Equals(this) => Self::Equals(this.transform(f)),
        }
    }
}

impl<T: Term + fmt::Display> fmt::Display for Atomic<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atomic::Atom(this) => this.fmt(f),
            Atomic::Equals(this) => this.fmt(f),
        }
    }
}
