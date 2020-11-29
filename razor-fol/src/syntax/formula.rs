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
            QFF::Atom(this) => Atom {
                predicate: this.predicate.clone(),
                terms: this.terms.iter().map(f).collect(),
            }
            .into(),
            QFF::Equals(this) => Equals {
                left: f(&this.left),
                right: f(&this.right),
            }
            .into(),
            QFF::Not(this) => Not {
                formula: this.formula.transform(f),
            }
            .into(),
            QFF::And(this) => And {
                left: this.left.transform(f),
                right: this.right.transform(f),
            }
            .into(),
            QFF::Or(this) => Or {
                left: this.left.transform(f),
                right: this.right.transform(f),
            }
            .into(),
            QFF::Implies(this) => Implies {
                premise: this.premise.transform(f),
                consequence: this.consequence.transform(f),
            }
            .into(),
            QFF::Iff(this) => Iff {
                left: this.left.transform(f),
                right: this.right.transform(f),
            }
            .into(),
        }
    }

    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self {
        // this does not rename bound variables of the formula
        self.transform(&|t: &Term| t.rename_vars(renaming))
    }

    fn substitute(&self, substitution: &impl Substitution) -> Self {
        self.transform(&|t: &Term| t.substitute(substitution))
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
