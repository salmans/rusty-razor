/*! Introduces an abstraction for formulae and various types of connectives as ingredients
for constructing formulae.*/
use super::{Pred, Term, V};
use crate::transform::{Substitution, TermBased, VariableRenaming};
use itertools::Itertools;

/// Is the trait of formulae, including first-order formulae.
pub trait Formula {
    /// Returns a list of free variable symbols in the receiver formula.
    ///
    /// **Note**: In the list of free variables, each variable symbol appears only once
    /// even if it is present at multiple positions of the receiver formula.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{V, FOF};
    /// # use itertools::Itertools;
    /// use razor_fol::syntax::Formula;
    ///
    /// // `x`, `y` and `z` are variable symbols:
    /// let x = V::from("x");
    /// let y = V::from("y");
    /// let z = V::from("z");
    ///
    /// // (P(x) ∧ Q(x, f(g(x), y))) ∨ ('c = g(z))
    /// let formula: FOF = "(P(x) & Q(x, f(g(x), y))) |  'c = g(z)".parse().unwrap();
    /// assert_eq!(vec![&x, &y, &z].iter().sorted(), formula.free_vars().iter().sorted());
    ///
    /// // ∀ x. P(x, y)
    /// let formula: FOF = "forall x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars()); // FOF is a Formula
    ///
    /// // ∃ x. P(x, y)
    /// let formula: FOF = "exists x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars());
    /// ```    
    fn free_vars(&self) -> Vec<&V>;
}

/// Represents an atomic formula, obtained by applying a predicate on a list of terms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Atom {
    pub predicate: Pred,
    pub terms: Vec<Term>,
}

impl Formula for Atom {
    fn free_vars(&self) -> Vec<&V> {
        self.terms
            .iter()
            .flat_map(|t| t.free_vars())
            .unique()
            .collect()
    }
}

impl TermBased for Atom {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            predicate: self.predicate.clone(),
            terms: self.terms.iter().map(f).collect(),
        }
    }
}

/// Represents an equation between two terms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Equals {
    pub left: Term,
    pub right: Term,
}

impl Formula for Equals {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }
}

impl TermBased for Equals {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            left: f(&self.left),
            right: f(&self.right),
        }
    }
}

/// Represents the negation of a formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Not<F: Formula> {
    pub formula: F,
}

impl<F: Formula> Formula for Not<F> {
    fn free_vars(&self) -> Vec<&V> {
        self.formula.free_vars()
    }
}

impl<F: Formula + TermBased> TermBased for Not<F> {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Not {
            formula: self.formula.transform(f),
        }
    }
}

/// Represents the conjunction of two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct And<F: Formula> {
    pub left: F,
    pub right: F,
}

impl<F: Formula> Formula for And<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }
}

impl<F: Formula + TermBased> TermBased for And<F> {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

/// Represents the disjunction of two formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Or<F: Formula> {
    pub left: F,
    pub right: F,
}

impl<F: Formula> Formula for Or<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }
}

impl<F: Formula + TermBased> TermBased for Or<F> {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

/// Represents an implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Implies<F: Formula> {
    pub premise: F,
    pub consequence: F,
}

impl<F: Formula> Formula for Implies<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.premise.free_vars();
        vs.extend(self.consequence.free_vars());
        vs.into_iter().unique().collect()
    }
}

impl<F: Formula + TermBased> TermBased for Implies<F> {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            premise: self.premise.transform(f),
            consequence: self.consequence.transform(f),
        }
    }
}

/// Represents a bi-implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Iff<F: Formula> {
    pub left: F,
    pub right: F,
}

impl<F: Formula> Formula for Iff<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }
}

impl<F: Formula + TermBased> TermBased for Iff<F> {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            left: self.left.transform(f),
            right: self.right.transform(f),
        }
    }
}

/// Represents an existentially quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Exists<F: Formula> {
    pub variables: Vec<V>,
    pub formula: F,
}

impl<F: Formula> Formula for Exists<F> {
    fn free_vars(&self) -> Vec<&V> {
        self.formula
            .free_vars()
            .into_iter()
            .filter(|v| !self.variables.contains(v))
            .collect()
    }
}

impl<F: Formula + TermBased> TermBased for Exists<F> {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            variables: self.variables.clone(),
            formula: self.formula.transform(f),
        }
    }
}

/// Represents a universally quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Forall<F: Formula> {
    pub variables: Vec<V>,
    pub formula: F,
}

impl<F: Formula> Formula for Forall<F> {
    fn free_vars(&self) -> Vec<&V> {
        self.formula
            .free_vars()
            .into_iter()
            .filter(|v| !self.variables.contains(v))
            .collect()
    }
}

impl<F: Formula + TermBased> TermBased for Forall<F> {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            variables: self.variables.clone(),
            formula: self.formula.transform(f),
        }
    }
}

/// A literal is either an atomic formula [`Atom`] or its negation. Because we treat
/// equality as a special case of an atomic formula, a literal may contain an [`Equals`] or
/// its negation as well.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Literal {
    /// Wraps a (positive) atomic formula of type [`Atom`].
    Atom(Atom),

    /// Wraps the negation of an atomic formula of type [`Atom`].    
    Neg(Atom),

    /// Wraps a (positive) equality of type [`Equals`].
    Equals(Equals),

    /// Wraps the nagation of an equality of type [`Equals`].
    Neq(Equals),
}

impl Formula for Literal {
    fn free_vars(&self) -> Vec<&V> {
        match self {
            Literal::Atom(this) => this.free_vars(),
            Literal::Neg(this) => this.free_vars(),
            Literal::Equals(this) => this.free_vars(),
            Literal::Neq(this) => this.free_vars(),
        }
    }
}

impl From<Atom> for Literal {
    fn from(value: Atom) -> Self {
        Self::Atom(value)
    }
}

impl From<Not<Atom>> for Literal {
    fn from(value: Not<Atom>) -> Self {
        Self::Neg(value.formula)
    }
}

impl From<Equals> for Literal {
    fn from(value: Equals) -> Self {
        Self::Equals(value)
    }
}

impl From<Not<Equals>> for Literal {
    fn from(value: Not<Equals>) -> Self {
        Self::Neq(value.formula)
    }
}

impl TermBased for Literal {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        match self {
            Literal::Atom(this) => this.transform(f).into(),
            Literal::Neg(this) => this.transform(f).into(),
            Literal::Equals(this) => this.transform(f).into(),
            Literal::Neq(this) => this.transform(f).into(),
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
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
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

    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self {
        self.transform(&|t: &Term| t.rename_vars(renaming))
    }

    fn substitute(&self, sub: &impl Substitution) -> Self {
        self.transform(&|t: &Term| t.substitute(sub))
    }
}

impl Formula for QFF {
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
}
