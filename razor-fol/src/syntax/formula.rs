/*! Introduces an abstraction for formulae and various types of connectives as ingredients for
constructing formulae.*/
use super::{Pred, Term, V};
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Atom {
    predicate: Pred,
    terms: Vec<Term>,
}

impl Atom {
    /// Creates a new atom.
    pub fn new(predicate: Pred, terms: Vec<Term>) -> Self {
        Self { predicate, terms }
    }

    /// Returns the predicate of the receiver.
    #[inline(always)]
    pub fn predicate(&self) -> &Pred {
        &self.predicate
    }

    /// Returns the terms of the receiver.
    #[inline(always)]
    pub fn terms(&self) -> &[Term] {
        &self.terms
    }
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Equals {
    left: Term,
    right: Term,
}

impl Equals {
    /// Creates a new equation.
    pub fn new(left: Term, right: Term) -> Self {
        Self { left, right }
    }

    /// Returns the term on the left of the equation.
    #[inline(always)]
    pub fn left(&self) -> &Term {
        &self.left
    }

    /// Returns the term on the right of the equation.
    #[inline(always)]
    pub fn right(&self) -> &Term {
        &self.right
    }
}

impl Formula for Equals {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }
}

/// Represents the negation of a formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Not<F: Formula> {
    formula: F,
}

impl<F: Formula> Not<F> {
    /// Wraps `formula` in a new instance of [`Not`].
    pub fn new(formula: F) -> Self {
        Self { formula }
    }

    /// Returns the formula wrapped in the receiver.
    #[inline(always)]
    pub fn formula(&self) -> &F {
        &self.formula
    }
}

impl<F: Formula> Formula for Not<F> {
    fn free_vars(&self) -> Vec<&V> {
        self.formula.free_vars()
    }
}

/// Represents the conjunction of two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct And<F: Formula> {
    left: F,
    right: F,
}

impl<F: Formula> And<F> {
    /// Returns the conjunction of `left` and `right`.
    pub fn new(left: F, right: F) -> Self {
        Self { left, right }
    }

    /// Returns the formula on the left of the receiver.
    #[inline(always)]
    pub fn left(&self) -> &F {
        &self.left
    }

    /// Returns the formula on the right of the receiver.
    #[inline(always)]
    pub fn right(&self) -> &F {
        &self.right
    }
}

impl<F: Formula> Formula for And<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }
}

/// Represents the disjunction of two formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Or<F: Formula> {
    left: F,
    right: F,
}

impl<F: Formula> Or<F> {
    /// Returns the disjuction of `left` and `right`.    
    pub fn new(left: F, right: F) -> Self {
        Self { left, right }
    }

    /// Returns the formula on the left of the receiver.
    #[inline(always)]
    pub fn left(&self) -> &F {
        &self.left
    }

    /// Returns the formula on the right of the receiver.
    #[inline(always)]
    pub fn right(&self) -> &F {
        &self.right
    }
}

impl<F: Formula> Formula for Or<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }
}

/// Represents an implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Implies<F: Formula> {
    premise: F,
    consequence: F,
}

impl<F: Formula> Implies<F> {
    /// Returns an implication with a `premise` and a `consequence`.
    pub fn new(premise: F, consequence: F) -> Self {
        Self {
            premise,
            consequence,
        }
    }

    /// Returns the premise of the receiver.
    #[inline(always)]
    pub fn premise(&self) -> &F {
        &self.premise
    }

    /// Returns the consequence of the receiver.
    #[inline(always)]
    pub fn consequence(&self) -> &F {
        &self.consequence
    }
}

impl<F: Formula> Formula for Implies<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.premise.free_vars();
        vs.extend(self.consequence.free_vars());
        vs.into_iter().unique().collect()
    }
}

/// Represents a bi-implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Iff<F: Formula> {
    left: F,
    right: F,
}

impl<F: Formula> Iff<F> {
    /// Returns a bi-implication between `left` and `rigth`.
    pub fn new(left: F, right: F) -> Self {
        Self { left, right }
    }

    /// Returns the formula on left of the receiver.
    #[inline(always)]
    pub fn left(&self) -> &F {
        &self.left
    }

    /// Returns the formula on the right of the receiver.
    #[inline(always)]
    pub fn right(&self) -> &F {
        &self.right
    }
}

impl<F: Formula> Formula for Iff<F> {
    fn free_vars(&self) -> Vec<&V> {
        let mut vs = self.left.free_vars();
        vs.extend(self.right.free_vars());
        vs.into_iter().unique().collect()
    }
}

/// Represents an existentially quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Exists<F: Formula> {
    variables: Vec<V>,
    formula: F,
}

impl<F: Formula> Exists<F> {
    /// Returns an existentially quantified formula with bound `variables` and `formula`.
    pub fn new(variables: Vec<V>, formula: F) -> Self {
        Self { variables, formula }
    }

    /// Returns the bound variables of the receiver.
    #[inline(always)]
    pub fn variables(&self) -> &[V] {
        &self.variables
    }

    /// Returns the formula of the existentially quantified receiver.
    #[inline(always)]
    pub fn formula(&self) -> &F {
        &self.formula
    }
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Forall<F: Formula> {
    variables: Vec<V>,
    formula: F,
}

impl<F: Formula> Forall<F> {
    /// Returns a universally quantified formula with bound `variables` and `formula`.    
    pub fn new(variables: Vec<V>, formula: F) -> Self {
        Self { variables, formula }
    }

    /// Returns the bound variables of the receiver.
    #[inline(always)]
    pub fn variables(&self) -> &[V] {
        &self.variables
    }

    /// Returns the formula of the universally quantified receiver.
    #[inline(always)]
    pub fn formula(&self) -> &F {
        &self.formula
    }
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
