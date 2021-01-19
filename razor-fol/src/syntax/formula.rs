/*! Introduces an abstraction for formulae and various generic types as building blocks
of formula types.*/
pub mod clause;
pub mod fof;
pub mod qff;

use super::{
    signature::PSig,
    term::{Renaming, Substitution},
    Error, Pred, Sig, Term, Var, EQ_SYM,
};
use itertools::Itertools;
use std::{fmt, hash::Hash};

// Precedence of basic formula types:
pub(crate) const PRECEDENCE_AND: u8 = 7;
pub(crate) const PRECEDENCE_OR: u8 = 7;
pub(crate) const PRECEDENCE_IMPLIES: u8 = 7;
pub(crate) const PRECEDENCE_IFF: u8 = 7;
pub(crate) const PRECEDENCE_EXISTS: u8 = 7;
pub(crate) const PRECEDENCE_FORALL: u8 = 7;
pub(crate) const PRECEDENCE_EQUALS: u8 = 8;
pub(crate) const PRECEDENCE_NOT: u8 = 9;
pub(crate) const PRECEDENCE_ATOM: u8 = 10;

/// Is the trait of various formula types.
pub trait Formula {
    /// Is the type of [`Term`]s in this type of formula.
    type Term: Term;

    /// Returns the signature on which the formula is defined. It fails if there are
    /// the underlying signature is inconsistent.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{Var, FOF, Func};
    /// # use std::{collections::HashSet, iter::FromIterator};
    /// use razor_fol::syntax::Formula;
    ///
    /// let fof: FOF = "(P(x) ∧ Q(x, f(g(x), y))) ∨  'c = g(z)".parse().unwrap();
    /// let signature = fof.signature().unwrap();
    /// assert_eq!(&HashSet::from_iter(vec!["c".into()]), signature.constants());
    /// assert_eq!(Func::from("f"), signature.functions().get("f").unwrap().symbol);
    /// assert_eq!(2, signature.predicates().get("Q").unwrap().arity);
    ///
    /// let fof: FOF = "P(x) ∧ P(g(x), y)".parse().unwrap();
    /// let signature = fof.signature().is_err(); // inconsistent arity for `P`
    /// ```    
    fn signature(&self) -> Result<Sig, Error>;

    /// Returns a list of free the variable symbols present in the receiver.
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
    /// let formula: FOF = "(P(x) & Q(x, f(g(x), y))) |  'c = g(z)".parse().unwrap();
    /// assert_eq!(vec![&x, &y, &z].iter().sorted(), formula.free_vars().iter().sorted());
    ///
    /// let formula: FOF = "forall x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars());
    ///
    /// let formula: FOF = "exists x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars());
    /// ```    
    fn free_vars(&self) -> Vec<&Var>;

    /// Applies a transformation function `f` on the terms of the receiver.
    fn transform(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self;

    /// Recursively applies a [`Renaming`] on the variable terms of the receiver.
    fn rename_vars(&self, renaming: &impl Renaming) -> Self
    where
        Self: Sized,
    {
        self.transform(&|t: &Self::Term| t.rename_vars(renaming))
    }

    /// Recursively applies a [`Substitution`] on the variable terms of the receiver.
    fn substitute(&self, sub: &impl Substitution<Self::Term>) -> Self
    where
        Self: Sized,
    {
        self.transform(&|t: &Self::Term| t.substitute(sub))
    }
}

// Extension to `Formula` for internal use only.
pub trait FormulaEx: Formula {
    // Precedence of the formula, used for parenthesizing pretty printing.
    fn precedence(&self) -> u8;
}

/// Represents an atomic formula, obtained by applying a predicate on a list of terms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

        for t in &self.terms {
            sig = sig.merge(t.signature()?)?;
        }
        sig.add_predicate(PSig {
            symbol: self.predicate.clone(),
            arity: self.terms.len() as u8,
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

impl<T: Term> FormulaEx for Atom<T> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_ATOM
    }
}

impl<T: Term + fmt::Display> fmt::Display for Atom<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ts = self.terms.iter().map(|t| t.to_string()).collect_vec();
        write!(f, "{}({})", self.predicate.to_string(), ts.join(", "))
    }
}

impl<T: Term + fmt::Debug> fmt::Debug for Atom<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ts = self.terms.iter().map(|t| format!("{:?}", t)).collect_vec();
        write!(f, "{}({})", self.predicate.to_string(), ts.join(", "))
    }
}

/// Represents an equation between two terms.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<T: Term> FormulaEx for Equals<T> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_EQUALS
    }
}

impl<T: Term + fmt::Display> fmt::Display for Equals<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.left, self.right)
    }
}

impl<T: Term + fmt::Debug> fmt::Debug for Equals<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} = {:?}", self.left, self.right)
    }
}

/// Represents the negation of a formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<F: Formula> FormulaEx for Not<F> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_NOT
    }
}

impl<F: FormulaEx + fmt::Display> fmt::Display for Not<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.precedence() >= self.formula.precedence() {
            write!(f, "¬({})", self.formula)
        } else {
            write!(f, "¬{}", self.formula)
        }
    }
}

impl<F: FormulaEx + fmt::Debug> fmt::Debug for Not<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.precedence() >= self.formula.precedence() {
            write!(f, "~({:?})", self.formula)
        } else {
            write!(f, "~{:?}", self.formula)
        }
    }
}

/// Represents the conjunction of two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<F: Formula> FormulaEx for And<F> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_AND
    }
}

impl<F: FormulaEx + fmt::Display> fmt::Display for And<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let left = self.precedence() >= self.left.precedence();
        let right = self.precedence() >= self.right.precedence();
        match (left, right) {
            (false, false) => write!(f, "{} ∧ {}", self.left, self.right),
            (false, true) => write!(f, "{} ∧ ({})", self.left, self.right),
            (true, false) => write!(f, "({}) ∧ {}", self.left, self.right),
            (true, true) => write!(f, "({}) ∧ ({})", self.left, self.right),
        }
    }
}

impl<F: FormulaEx + fmt::Debug> fmt::Debug for And<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let left = self.precedence() >= self.left.precedence();
        let right = self.precedence() >= self.right.precedence();
        match (left, right) {
            (false, false) => write!(f, "{:?} & {:?}", self.left, self.right),
            (false, true) => write!(f, "{:?} & ({:?})", self.left, self.right),
            (true, false) => write!(f, "({:?}) & {:?}", self.left, self.right),
            (true, true) => write!(f, "({:?}) & ({:?})", self.left, self.right),
        }
    }
}

/// Represents the disjunction of two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<F: Formula> FormulaEx for Or<F> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_OR
    }
}

impl<F: FormulaEx + fmt::Display> fmt::Display for Or<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let left = self.precedence() >= self.left.precedence();
        let right = self.precedence() >= self.right.precedence();
        match (left, right) {
            (false, false) => write!(f, "{} ∨ {}", self.left, self.right),
            (false, true) => write!(f, "{} ∨ ({})", self.left, self.right),
            (true, false) => write!(f, "({}) ∨ {}", self.left, self.right),
            (true, true) => write!(f, "({}) ∨ ({})", self.left, self.right),
        }
    }
}

impl<F: FormulaEx + fmt::Debug> fmt::Debug for Or<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let left = self.precedence() >= self.left.precedence();
        let right = self.precedence() >= self.right.precedence();
        match (left, right) {
            (false, false) => write!(f, "{:?} | {:?}", self.left, self.right),
            (false, true) => write!(f, "{:?} | ({:?})", self.left, self.right),
            (true, false) => write!(f, "({:?}) | {:?}", self.left, self.right),
            (true, true) => write!(f, "({:?}) | ({:?})", self.left, self.right),
        }
    }
}

/// Represents an implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<F: Formula> FormulaEx for Implies<F> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_IMPLIES
    }
}

impl<F: FormulaEx + fmt::Display> fmt::Display for Implies<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let premise = self.precedence() >= self.premise.precedence();
        let consequence = self.precedence() >= self.consequence.precedence();
        match (premise, consequence) {
            (false, false) => write!(f, "{} → {}", self.premise, self.consequence),
            (false, true) => write!(f, "{} → ({})", self.premise, self.consequence),
            (true, false) => write!(f, "({}) → {}", self.premise, self.consequence),
            (true, true) => write!(f, "({}) → ({})", self.premise, self.consequence),
        }
    }
}

impl<F: FormulaEx + fmt::Debug> fmt::Debug for Implies<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let premise = self.precedence() >= self.premise.precedence();
        let consequence = self.precedence() >= self.consequence.precedence();
        match (premise, consequence) {
            (false, false) => write!(f, "{:?} -> {:?}", self.premise, self.consequence),
            (false, true) => write!(f, "{:?} -> ({:?})", self.premise, self.consequence),
            (true, false) => write!(f, "({:?}) -> {:?}", self.premise, self.consequence),
            (true, true) => write!(f, "({:?}) -> ({:?})", self.premise, self.consequence),
        }
    }
}

/// Represents a bi-implication between two formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<F: Formula> FormulaEx for Iff<F> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_IFF
    }
}

impl<F: FormulaEx + fmt::Display> fmt::Display for Iff<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let left = self.precedence() >= self.left.precedence();
        let right = self.precedence() >= self.right.precedence();
        match (left, right) {
            (false, false) => write!(f, "{} ⇔ {}", self.left, self.right),
            (false, true) => write!(f, "{} ⇔ ({})", self.left, self.right),
            (true, false) => write!(f, "({}) ⇔ {}", self.left, self.right),
            (true, true) => write!(f, "({}) ⇔ ({})", self.left, self.right),
        }
    }
}

impl<F: FormulaEx + fmt::Debug> fmt::Debug for Iff<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let left = self.precedence() >= self.left.precedence();
        let right = self.precedence() >= self.right.precedence();
        match (left, right) {
            (false, false) => write!(f, "{:?} <=> {:?}", self.left, self.right),
            (false, true) => write!(f, "{:?} <=> ({:?})", self.left, self.right),
            (true, false) => write!(f, "({:?}) <=> {:?}", self.left, self.right),
            (true, true) => write!(f, "({:?}) <=> ({:?})", self.left, self.right),
        }
    }
}

/// Represents an existentially quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<F: Formula> FormulaEx for Exists<F> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_EXISTS
    }
}

impl<F: FormulaEx + fmt::Display> fmt::Display for Exists<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vs = self.variables.iter().map(|t| t.to_string()).collect_vec();
        if self.precedence() >= self.formula.precedence() {
            write!(f, "∃ {}. ({})", vs.join(", "), self.formula)
        } else {
            write!(f, "∃ {}. {}", vs.join(", "), self.formula)
        }
    }
}

impl<F: FormulaEx + fmt::Debug> fmt::Debug for Exists<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vs = self.variables.iter().map(|t| t.to_string()).collect_vec();
        if self.precedence() >= self.formula.precedence() {
            write!(f, "? {}. ({:?})", vs.join(", "), self.formula)
        } else {
            write!(f, "? {}. {:?}", vs.join(", "), self.formula)
        }
    }
}

/// Represents a universally quantified formula.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<F: Formula> FormulaEx for Forall<F> {
    fn precedence(&self) -> u8 {
        PRECEDENCE_FORALL
    }
}

impl<F: FormulaEx + fmt::Display> fmt::Display for Forall<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vs: Vec<_> = self.variables.iter().map(|t| t.to_string()).collect();
        if self.precedence() >= self.formula.precedence() {
            write!(f, "∀ {}. ({})", vs.join(", "), self.formula)
        } else {
            write!(f, "∀ {}. {}", vs.join(", "), self.formula)
        }
    }
}

impl<F: FormulaEx + fmt::Debug> fmt::Debug for Forall<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vs: Vec<_> = self.variables.iter().map(|t| t.to_string()).collect();
        if self.precedence() >= self.formula.precedence() {
            write!(f, "! {}. ({:?})", vs.join(", "), self.formula)
        } else {
            write!(f, "! {}. {:?}", vs.join(", "), self.formula)
        }
    }
}

/// Is an atomic formula that wraps an instance of either [`Atom`] or [`Equals`].
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<T: Term + fmt::Debug> fmt::Debug for Atomic<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atomic::Atom(this) => this.fmt(f),
            Atomic::Equals(this) => this.fmt(f),
        }
    }
}

impl<T: Term> FormulaEx for Atomic<T> {
    fn precedence(&self) -> u8 {
        match self {
            Atomic::Atom(this) => this.precedence(),
            Atomic::Equals(this) => this.precedence(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assert_eq_sorted_vecs, fof,
        syntax::{
            signature::{FSig, PSig},
            term::Complex,
            Const, Func, Sig,
        },
        term, v,
    };

    #[test]
    fn atom_to_string() {
        assert_eq!(
            "R()",
            Atom::<Complex> {
                predicate: "R".into(),
                terms: vec![],
            }
            .to_string()
        );
        assert_eq!(
            "R(x, y)",
            Atom {
                predicate: "R".into(),
                terms: vec![term!(x), term!(y)],
            }
            .to_string()
        );
    }

    #[test]
    fn atom_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Atom::<Complex> {
                    predicate: "R".into(),
                    terms: vec![],
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![term!(y), term!(g(x, z))],
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![term!(z), term!(f(f(f(f(f(f(x)))))))],
                }
                .free_vars()
            );
        }
    }

    #[test]
    fn atom_transform() {
        let formula = Atom {
            predicate: "P".into(),
            terms: vec![term!(f(x)), term!(y)],
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            Atom {
                predicate: "P".into(),
                terms: vec![term!(z), term!(y)],
            },
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
            let formula = Atom {
                predicate: "P".into(),
                terms: vec![term!(@c)],
            };
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
            let formula = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x, @c))],
            };
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
            let formula = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x, @c)), term!(@d), term!(f(g(x), y))],
            };
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(f(y))],
            };
            assert!(formula.signature().is_ok());
        }
        {
            let formula = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(f(x, y))],
            };
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn equals_to_string() {
        assert_eq!(
            "x = y",
            Equals {
                left: term!(x),
                right: term!(y),
            }
            .to_string()
        );
    }

    #[test]
    fn equals_free_vars() {
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Equals {
                    left: term!(x),
                    right: term!(y),
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Equals {
                    left: term!(x),
                    right: term!(g()),
                }
                .free_vars()
            );
        }
    }

    #[test]
    fn equals_transform() {
        let formula = Equals {
            left: term!(f(x)),
            right: term!(y),
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            Equals {
                left: term!(z),
                right: term!(y),
            },
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
            let formula = Equals {
                left: term!(@c),
                right: term!(@c),
            };
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = Equals {
                left: term!(f(x)),
                right: term!(f(y)),
            };
            assert!(formula.signature().is_ok());
        }
        {
            let formula = Equals {
                left: term!(f(x)),
                right: term!(f(x, y)),
            };
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn not_to_string() {
        assert_eq!(
            "¬R(x, y)",
            Not {
                formula: fof!(R(x, y))
            }
            .to_string()
        );
    }

    #[test]
    fn not_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(expected, Not { formula: fof!(R()) }.free_vars());
        }
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Not {
                    formula: fof!(~(R()))
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Not {
                    formula: fof!((x) = (y))
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Not {
                    formula: fof!(R(x, y))
                }
                .free_vars()
            );
        }
    }

    #[test]
    fn not_transform() {
        let formula = Not {
            formula: fof!(R(f(x), y)),
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            Not {
                formula: fof!(R(z, y)),
            },
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
        let formula = Not {
            formula: fof!(P(f(@c), y)),
        };
        assert_eq!(sig, formula.signature().unwrap());
    }

    #[test]
    fn and_to_string() {
        assert_eq!(
            "P() ∧ Q()",
            And {
                left: fof!(P()),
                right: fof!(Q()),
            }
            .to_string()
        );
    }

    #[test]
    fn and_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                And {
                    left: fof!(P()),
                    right: fof!(Q()),
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                And {
                    left: fof!(P(z, y)),
                    right: fof!((x) = (y)),
                }
                .free_vars(),
            );
        }
    }

    #[test]
    fn and_transform() {
        let formula = And {
            left: fof!(P(f(x))),
            right: fof!(Q(y)),
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            And {
                left: fof!(P(z)),
                right: fof!(Q(y)),
            },
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
            let formula = And {
                left: fof!(P(f(x), y)),
                right: fof!(Q(@c)),
            };
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = And {
                left: fof!(P(x)),
                right: fof!(P(x, y)),
            };
            assert!(formula.signature().is_err());
        }
        {
            let formula = And {
                left: fof!(P(f(x))),
                right: fof!(P(f(y))),
            };
            assert!(formula.signature().is_ok());
        }
        {
            let formula = And {
                left: fof!(P(f(x))),
                right: fof!(P(f(x, y))),
            };
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn or_to_string() {
        assert_eq!(
            "P() ∨ Q()",
            Or {
                left: fof!(P()),
                right: fof!(Q()),
            }
            .to_string()
        );
    }

    #[test]
    fn or_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Or {
                    left: fof!(P()),
                    right: fof!(Q())
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Or {
                    left: fof!(P(z, y)),
                    right: fof!((x) = (y))
                }
                .free_vars(),
            );
        }
    }

    #[test]
    fn or_transform() {
        let formula = Or {
            left: fof!(P(f(x))),
            right: fof!(Q(y)),
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            Or {
                left: fof!(P(z)),
                right: fof!(Q(y)),
            },
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
            let formula = Or {
                left: fof!(P(f(x), y)),
                right: fof!(Q(@c)),
            };
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = Or {
                left: fof!(P(x)),
                right: fof!(P(x, y)),
            };
            assert!(formula.signature().is_err());
        }
        {
            let formula = Or {
                left: fof!(P(f(x))),
                right: fof!(P(f(y))),
            };
            assert!(formula.signature().is_ok());
        }
        {
            let formula = Or {
                left: fof!(P(f(x))),
                right: fof!(P(f(x, y))),
            };
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn implies_to_string() {
        assert_eq!(
            "P() → Q()",
            Implies {
                premise: fof!(P()),
                consequence: fof!(Q()),
            }
            .to_string()
        );
    }

    #[test]
    fn implies_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Implies {
                    premise: fof!(P()),
                    consequence: fof!(Q())
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Implies {
                    premise: fof!(P(z, y)),
                    consequence: fof!((x) = (y))
                }
                .free_vars(),
            );
        }
    }

    #[test]
    fn implies_transform() {
        let formula = Implies {
            premise: fof!(P(f(x))),
            consequence: fof!(Q(y)),
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            Implies {
                premise: fof!(P(z)),
                consequence: fof!(Q(y)),
            },
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
            let formula = Implies {
                premise: fof!(P(f(x), y)),
                consequence: fof!(Q(@c)),
            };
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = Implies {
                premise: fof!(P(x)),
                consequence: fof!(P(x, y)),
            };
            assert!(formula.signature().is_err());
        }
        {
            let formula = Implies {
                premise: fof!(P(f(x))),
                consequence: fof!(P(f(y))),
            };
            assert!(formula.signature().is_ok());
        }
        {
            let formula = Implies {
                premise: fof!(P(f(x))),
                consequence: fof!(P(f(x, y))),
            };
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn iff_to_string() {
        assert_eq!(
            "P() ⇔ Q()",
            Iff {
                left: fof!(P()),
                right: fof!(Q())
            }
            .to_string()
        );
    }

    #[test]
    fn iff_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Iff {
                    left: fof!(P()),
                    right: fof!(Q()),
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Iff {
                    left: fof!(P(z, y)),
                    right: fof!((x) = (y)),
                }
                .free_vars(),
            );
        }
    }

    #[test]
    fn iff_transform() {
        let formula = Iff {
            left: fof!(P(f(x))),
            right: fof!(Q(y)),
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            Iff {
                left: fof!(P(z)),
                right: fof!(Q(y)),
            },
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
            let formula = Iff {
                left: fof!(P(f(x), y)),
                right: fof!(Q(@c)),
            };
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = Iff {
                left: fof!(P(x)),
                right: fof!(P(x, y)),
            };
            assert!(formula.signature().is_err());
        }
        {
            let formula = Iff {
                left: fof!(P(f(x))),
                right: fof!(P(f(y))),
            };
            assert!(formula.signature().is_ok());
        }
        {
            let formula = Iff {
                left: fof!(P(f(x))),
                right: fof!(P(f(x, y))),
            };
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn exists_to_string() {
        assert_eq!(
            "∃ x. P(x)",
            Exists {
                variables: vec![v!(x)],
                formula: fof!(P(x)),
            }
            .to_string()
        );
        assert_eq!(
            "∃ x, y. P(x, y)",
            Exists {
                variables: vec![v!(x), v!(y)],
                formula: fof!(P(x, y)),
            }
            .to_string()
        );
    }

    #[test]
    fn exists_transform() {
        let formula = Exists {
            variables: vec![v!(x)],
            formula: fof!(Q(f(x), y)),
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            Exists {
                variables: vec![v!(x)],
                formula: fof!(Q(z, y)),
            },
            formula.transform(&f)
        );
    }

    #[test]
    fn exists_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Exists {
                    variables: vec![v!(x)],
                    formula: fof!(P(x))
                }
                .free_vars()
            );
        }
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Exists {
                    variables: vec![v!(x), v!(y)],
                    formula: fof!(P(x, y))
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Exists {
                    variables: vec![v!(x)],
                    formula: fof!((x) = (y))
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Exists {
                    variables: vec![v!(x)],
                    formula: fof!((Q(x)) & (R(y)))
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Exists {
                    variables: vec![v!(x)],
                    formula: fof!((Q(x, z)) & (R(x, y))),
                }
                .free_vars(),
            );
        }
    }

    #[test]
    fn exists_signature() {
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
        let formula = Exists {
            variables: vec![v!(x)],
            formula: fof!(P(f(@c), y)),
        };
        assert_eq!(sig, formula.signature().unwrap());
    }

    #[test]
    fn forall_to_string() {
        assert_eq!(
            "∀ x. P(x)",
            Forall {
                variables: vec![v!(x)],
                formula: fof!(P(x)),
            }
            .to_string()
        );
        assert_eq!(
            "∀ x, y. P(x, y)",
            Forall {
                variables: vec![v!(x), v!(y)],
                formula: fof!(P(x, y)),
            }
            .to_string()
        );
    }

    #[test]
    fn forall_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Forall {
                    variables: vec![v!(x)],
                    formula: fof!(P(x))
                }
                .free_vars()
            );
        }
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(
                expected,
                Forall {
                    variables: vec![v!(x), v!(y)],
                    formula: fof!(P(x, y))
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Forall {
                    variables: vec![v!(x)],
                    formula: fof!((x) = (y))
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Forall {
                    variables: vec![v!(x)],
                    formula: fof!((Q(x)) & (R(y)))
                }
                .free_vars()
            );
        }
        {
            let expected = vec![v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Forall {
                    variables: vec![v!(x)],
                    formula: fof!((Q(x, z)) & (R(x, y))),
                }
                .free_vars(),
            );
        }
    }

    #[test]
    fn forall_transform() {
        let formula = Forall {
            variables: vec![v!(x)],
            formula: fof!(Q(f(x), y)),
        };
        let f = |t: &Complex| {
            if t == &term!(f(x)) {
                term!(z)
            } else {
                t.clone()
            }
        };
        assert_eq!(
            Forall {
                variables: vec![v!(x)],
                formula: fof!(Q(z, y)),
            },
            formula.transform(&f)
        );
    }

    #[test]
    fn forall_signature() {
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
        let formula = Forall {
            variables: vec![v!(x)],
            formula: fof!(P(f(@c), y)),
        };
        assert_eq!(sig, formula.signature().unwrap());
    }

    #[test]
    fn atomic_to_string() {
        assert_eq!(
            "R(x, y)",
            Atomic::from(Atom {
                predicate: "R".into(),
                terms: vec![term!(x), term!(y)],
            })
            .to_string()
        );

        assert_eq!(
            "x = y",
            Atomic::from(Equals {
                left: term!(x),
                right: term!(y),
            })
            .to_string()
        );
    }

    #[test]
    fn atomic_free_vars() {
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Atomic::from(Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x), term!(y)],
                })
                .free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                Atomic::from(Equals {
                    left: term!(x),
                    right: term!(y),
                })
                .free_vars()
            );
        }
    }

    #[test]
    fn atomic_transform() {
        {
            let formula: Atomic<_> = Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(y)],
            }
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
                Atomic::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z), term!(y)],
                }),
                formula.transform(&f)
            );
        }
        {
            let formula: Atomic<_> = Equals {
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
                Atomic::from(Equals {
                    left: term!(z),
                    right: term!(y),
                }),
                formula.transform(&f)
            );
        }
    }

    #[test]
    fn atomic_signature() {
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
            let formula = Atomic::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x, @c))],
            });
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = Atomic::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(f(x, y))],
            });
            assert!(formula.signature().is_err());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from(EQ_SYM),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula = Atomic::from(Equals {
                left: term!(@c),
                right: term!(@c),
            });
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = Atomic::from(Equals {
                left: term!(f(x)),
                right: term!(f(x, y)),
            });
            assert!(formula.signature().is_err());
        }
    }
}
