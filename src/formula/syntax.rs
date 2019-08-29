/*! Defines an abstract syntax tree (AST) for first-order terms and formulae with equality. */
use itertools::Itertools;

use std::fmt;

/// Represents an uninterpreted function symbol with a given name.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F(String);

impl F {
    /// Applies the receiver on a list of terms. The length of `terms` must be equal to
    /// the (assumed) arity of the function.
    ///
    /// **Note**: the definition of [`F`] does not impose any restrictions on the
    /// arity of function symbols. The user is expected to assume the arity of the function.
    ///
    /// [`F`]: ./struct.F.html
    pub fn app<T: FApp>(self, terms: Vec<T>) -> T {
        T::apply(self, terms)
    }

    /// Applies the (nullary) function.
    pub fn app0<T: FApp>(self) -> T {
        T::apply(self, vec![])
    }

    /// Applies the (unary) receiver on a term.
    pub fn app1<T: FApp>(self, first: T) -> T {
        T::apply(self, vec![first])
    }

    /// Applies the (binary) receiver on two terms.
    pub fn app2<T: FApp>(self, first: T, second: T) -> T {
        T::apply(self, vec![first, second])
    }

    /// Applies the (ternary) receiver on three terms.
    pub fn app3<T: FApp>(self, first: T, second: T, third: T) -> T {
        T::apply(self, vec![first, second, third])
    }

    /// Applies the (4-ary) receiver on four terms.
    pub fn app4<T: FApp>(self, first: T, second: T, third: T, fourth: T) -> T {
        T::apply(self, vec![first, second, third, fourth])
    }

    /// Applies the (5-ary) receiver on five terms.
    pub fn app5<T: FApp>(self, first: T, second: T, third: T, fourth: T, fifth: T) -> T {
        T::apply(self, vec![first, second, third, fourth, fifth])
    }
}

impl From<&str> for F {
    fn from(name: &str) -> Self {
        Self(name.to_owned())
    }
}

// Deref coercion doesn't seem to be working for &String
impl From<&String> for F {
    fn from(name: &String) -> Self {
        Self(name.to_owned())
    }
}

impl fmt::Display for F {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for F {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Is the trait for types that can be passed to a function of type [`F`] as arguments.
///
/// [`F`]: ./struct.F.html
// TODO: at a syntactic level, Term implements FApp but at a semantic level WitnessTerm does
pub trait FApp: Sized {
    /// builds a complex term by applying `f` the `terms` as arguments.
    fn apply(function: F, terms: Vec<Self>) -> Self;
}

/// Represents a variable symbol with a given name.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct V(pub String);

impl From<&str> for V {
    fn from(name: &str) -> Self {
        Self(name.to_owned())
    }
}

impl From<&String> for V {
    fn from(name: &String) -> Self {
        Self(name.to_owned())
    }
}

impl fmt::Display for V {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for V {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Represents a constant symbol with a given name.
///
/// **Note**: Although it is possible to treat nullary functions as constants, we distinguish
/// the two at a syntactic level.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct C(String);

impl From<&str> for C {
    fn from(name: &str) -> Self {
        Self(name.to_owned())
    }
}

impl From<&String> for C {
    fn from(name: &String) -> Self {
        Self(name.to_owned())
    }
}

impl fmt::Display for C {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "'{}", self.0)
    }
}

impl fmt::Debug for C {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Represents a predicate symbol with a given name.
/// TODO: Rel is the semantic counterpart of Pred
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Pred(pub String);

impl Pred {
    /// Applies the receiver on a list of terms. The length of `terms` must be equal to
    /// the (assumed) arity of the predicate.
    ///
    /// **Note**: the definition of [`Pred`] does not impose any restrictions
    /// on the arity of predicate symbols. The user is expected to assume the arity of the predicate.
    ///
    /// [`Pred`]: ./struct.Pred.html
    pub fn app(self, terms: Vec<Term>) -> Formula {
        Formula::Atom { predicate: self, terms }
    }

    /// Applies the (nullary) receiver.
    pub fn app0(self) -> Formula {
        Formula::Atom { predicate: self, terms: vec![] }
    }

    /// Applies the (unary) receiver on a term.
    pub fn app1(self, first: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first] }
    }

    /// Applies the (binary) receiver on two terms.
    pub fn app2(self, first: Term, second: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first, second] }
    }

    /// Applies the (ternary) receiver on three terms.
    pub fn app3(self, first: Term, second: Term, third: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first, second, third] }
    }

    /// Applies the (4-ary) receiver on four terms.
    pub fn app4(self, first: Term, second: Term, third: Term, fourth: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first, second, third, fourth] }
    }

    /// Applies the (5-ary) receiver on five terms.
    pub fn app5(self, first: Term, second: Term, third: Term, fourth: Term, fifth: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first, second, third, fourth, fifth] }
    }
}

impl From<&str> for Pred {
    fn from(name: &str) -> Self {
        Self(name.to_owned())
    }
}

impl From<&String> for Pred {
    fn from(name: &String) -> Self {
        Self(name.to_owned())
    }
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Pred {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Represents a first-order term and consists of variables, constants and function applications.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    /// Is a variable term and is used to wrap a [variable symbol].
    ///
    /// [variable symbol]: ./struct.V.html
    Var { variable: V },

    /// Is a constant term and is used to wrap a [constant symbol].
    ///
    /// [constant symbol]: ./struct.C.html
    Const { constant: C },

    /// Is a complex term, made by applying a function on a list of terms.
    App { function: F, terms: Vec<Term> },
}

impl Term {
    /// Returns a list of all free variable symbols in the term.
    ///
    /// **Note**: Each variable symbol appears only once in the list of free variables even if it
    /// is present at multiple positions of the term.
    ///
    /// **Example**:
    /// ```rust
    /// # use rusty_razor::formula::syntax::{V, C, F, Term};
    /// # use itertools::Itertools;
    ///
    /// // `x_sym` and `y_sym` are variable symbols:
    /// let x_sym = V::from("x");
    /// let y_sym = V::from("y");
    ///
    /// // `c_sym` is a constant symbol:
    /// let c_sym = C::from("c");
    ///
    /// // `x` and `y` are variable terms:
    /// let x = Term::from(x_sym.clone());
    /// let y = Term::from(y_sym.clone());
    ///
    /// // `c` is a constant term:
    /// let c = Term::from(c_sym.clone());
    ///
    /// // `f` and `g` are function
    /// let f = F::from("f");
    /// let g = F::from("g");
    ///
    /// // f(x, g(y, c, x)):
    /// let t = f.app2(x.clone(), g.app3(y, c, x.clone()));
    ///
    /// // comparing the two (unordered) lists:
    /// assert_eq!(vec![&x_sym, &y_sym].iter().sorted(), t.free_vars().iter().sorted())
    /// ```
    pub fn free_vars(&self) -> Vec<&V> {
        match self {
            Term::Var { variable } => vec![variable],
            Term::Const { constant: _ } => vec![],
            Term::App { function: _, terms } => {
                terms.iter().flat_map(|t| t.free_vars()).into_iter().unique().collect()
            }
        }
    }

    /// Returns an equation (formula) between the receiver and `term`.
    pub fn equals(self, term: Term) -> Formula {
        Formula::Equals { left: self, right: term }
    }
}

impl From<V> for Term {
    fn from(variable: V) -> Self {
        Self::Var { variable }
    }
}

impl From<C> for Term {
    fn from(constant: C) -> Self {
        Self::Const { constant }
    }
}

// term is an FApp type.
impl FApp for Term {
    fn apply(function: F, terms: Vec<Term>) -> Self {
        Self::App { function, terms }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Var { variable } => write!(f, "{}", variable),
            Self::Const { constant } => write!(f, "{}", constant),
            Self::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", function, ts.join(", "))
            }
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Is an abstract syntax tree (AST) for representing first-order formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    /// Is logical Top (⊤) or Truth
    Top,

    /// Is logical Bottom (⟘) or Falsehood
    Bottom,

    /// Is an atomic formula, made by applying `predicate` on a `terms`.
    Atom { predicate: Pred, terms: Vec<Term> },

    /// Represents an equation among two terms.
    ///
    /// **Note**: Equation is treated as a special type of atomic formula.
    Equals { left: Term, right: Term },

    /// Constructs the negation of the `formula` that it holds.
    Not { formula: Box<Formula> },

    /// Makes a conjunction of the `left` and `right` formulae that it holds.
    And { left: Box<Formula>, right: Box<Formula> },

    /// Makes a disjunction of `left` and `right` formulae that it holds.
    Or { left: Box<Formula>, right: Box<Formula> },

    /// Makes an implication between `left` and `right` formulae that it holds.
    Implies { left: Box<Formula>, right: Box<Formula> },

    /// Makes a bi-implication between `left` and `right` formulae that it holds.
    Iff { left: Box<Formula>, right: Box<Formula> },

    /// Makes an existentially quantified formula with the bound `variables` and the `formula` that
    /// it holds.
    Exists { variables: Vec<V>, formula: Box<Formula> },

    /// Makes a universally quantified formula with the bound `variables` and the `formula` that
    /// it holds.
    Forall { variables: Vec<V>, formula: Box<Formula> },
}

/// Returns the negation of `formula`.
pub fn not(formula: Formula) -> Formula {
    Formula::Not { formula: Box::new(formula) }
}

/// Returns an existentially quantified formula with the given `variables` and `formula`.
pub fn exists(variables: Vec<V>, formula: Formula) -> Formula {
    Formula::Exists { variables, formula: Box::new(formula) }
}

/// Returns an existentially quantified formula on one variable.
pub fn exists1(first: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first], formula: Box::new(formula) }
}

/// Returns an existentially quantified formula on two variables.
pub fn exists2(first: V, second: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first, second], formula: Box::new(formula) }
}

/// Returns an existentially quantified formula on three variables.
pub fn exists3(first: V, second: V, third: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first, second, third], formula: Box::new(formula) }
}

/// Returns an existentially quantified formula on four variables.
pub fn exists4(first: V, second: V, third: V, fourth: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first, second, third, fourth], formula: Box::new(formula) }
}

/// Returns an existentially quantified formula on five variables.
pub fn exists5(first: V, second: V, third: V, fourth: V, fifth: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first, second, third, fourth, fifth], formula: Box::new(formula) }
}

/// Returns a universally quantified formula with the given `variables` and `formula`.
pub fn forall(variables: Vec<V>, formula: Formula) -> Formula {
    Formula::Forall { variables, formula: Box::new(formula) }
}

/// Returns a universally quantified formula on one variable.
pub fn forall1(first: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first], formula: Box::new(formula) }
}

/// Returns a universally quantified formula on two variables.
pub fn forall2(first: V, second: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first, second], formula: Box::new(formula) }
}

/// Returns a universally quantified formula on three variables.
pub fn forall3(first: V, second: V, third: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first, second, third], formula: Box::new(formula) }
}

/// Returns a universally quantified formula on four variables.
pub fn forall4(first: V, second: V, third: V, fourth: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first, second, third, fourth], formula: Box::new(formula) }
}

/// Returns a universally quantified formula on five variables.
pub fn forall5(first: V, second: V, third: V, fourth: V, fifth: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first, second, third, fourth, fifth], formula: Box::new(formula) }
}

impl Formula {
    /// Returns a conjunction of the receiver and `formula`.
    pub fn and(self, formula: Self) -> Self {
        Self::And { left: Box::new(self), right: Box::new(formula) }
    }

    /// Returns a disjunction of the receiver and `formula`.
    pub fn or(self, formula: Self) -> Self {
        Self::Or { left: Box::new(self), right: Box::new(formula) }
    }

    /// Returns an implication between the receiver and `formula`.
    pub fn implies(self, formula: Self) -> Self {
        Self::Implies { left: Box::new(self), right: Box::new(formula) }
    }

    /// Returns a bi-implication between the receiver and `formula`.
    pub fn iff(self, formula: Self) -> Self {
        Self::Iff { left: Box::new(self), right: Box::new(formula) }
    }

    /// Returns a list of free variable symbols in the receiver formula.
    ///
    /// **Note**: each variable symbol appears only once in the list of free variables even if it
    /// is present at multiple positions of the formula.
    ///
    /// **Example**:
    /// ```rust
    /// # use rusty_razor::formula::syntax::{V, Formula};
    /// # use itertools::Itertools;
    ///
    /// // `x`, `y` and `z` are variable symbols:
    /// let x = V::from("x");
    /// let y = V::from("y");
    /// let z = V::from("z");
    ///
    /// // (P(x) ∧ Q(x, f(g(x), y))) ∨ ('c = g(z))
    /// let formula: Formula = "(P(x) & Q(x, f(g(x), y))) |  'c = g(z)".parse().unwrap();
    /// assert_eq!(vec![&x, &y, &z].iter().sorted(), formula.free_vars().iter().sorted());
    ///
    /// // ∀ x. P(x, y)
    /// let formula: Formula = "forall x. P(x, y)".parse().unwrap();
    /// // notice that the bound variable `x` is not in the list of free variables of `formula`
    /// assert_eq!(vec![&y], formula.free_vars());
    ///
    /// // ∃ x. P(x, y)
    /// let formula: Formula = "exists x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars());
    /// ```
    pub fn free_vars(&self) -> Vec<&V> {
        match self {
            Self::Top => vec![],
            Self::Bottom => vec![],
            Self::Atom { predicate: _, terms } => {
                terms.iter().flat_map(|t| t.free_vars()).unique().collect()
            }
            Self::Equals { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Not { formula } => formula.free_vars(),
            Self::And { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Or { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Implies { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Iff { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Exists { variables, formula } => {
                formula.free_vars().into_iter().filter(|v| !variables.contains(v)).collect()
            }
            Self::Forall { variables, formula } => {
                formula.free_vars().into_iter().filter(|v| !variables.contains(v)).collect()
            }
        }
    }
}

// used for pretty printing a formula
impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fn parens(formula: &Formula) -> String {
            match formula {
                Formula::Top => formula.to_string(),
                Formula::Bottom => formula.to_string(),
                Formula::Atom { .. } => formula.to_string(),
                _ => format!("({})", formula),
            }
        }
        match self {
            Self::Top => write!(f, "{}", "⊤"),
            Self::Bottom => write!(f, "{}", "⟘"),
            Self::Atom { predicate, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", predicate.to_string(), ts.join(", "))
            }
            Self::Equals { left, right } => {
                write!(f, "{} = {}", left, right)
            }
            Self::Not { formula } => {
                write!(f, "¬{}", parens(formula))
            }
            Self::And { left, right } => {
                write!(f, "{} ∧ {}", parens(left), parens(right))
            }
            Self::Or { left, right } => {
                write!(f, "{} ∨ {}", parens(left), parens(right))
            }
            Self::Implies { left, right } => {
                write!(f, "{} → {}", parens(left), parens(right))
            }
            Self::Iff { left, right } => {
                write!(f, "{} ⇔ {}", parens(left), parens(right))
            }
            Self::Exists { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                write!(f, "∃ {}. {}", vs.join(", "), parens(formula))
            }
            Self::Forall { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                write!(f, "∀ {}. {}", vs.join(", "), parens(formula))
            }
        }
    }
}

// contains no non-ascii characters
impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        // a helper for writing binary formulas:
        fn write_binary
        (
            left: &Formula,
            right: &Formula,
            symbol: &str, f:
            &mut fmt::Formatter,
        ) -> Result<(), fmt::Error> {
            match left {
                Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                    match right {
                        Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                            write!(f, "{:?} {} {:?}", left, symbol, right)
                        }
                        _ => {
                            write!(f, "{:?} {} ({:?})", left, symbol, right)
                        }
                    }
                }
                _ => {
                    match right {
                        Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                            write!(f, "({:?}) {} {:?}", left, symbol, right)
                        }
                        _ => {
                            write!(f, "({:?}) {} ({:?})", left, symbol, right)
                        }
                    }
                }
            }
        }

        match self {
            Self::Top => write!(f, "{}", "TRUE"),
            Self::Bottom => write!(f, "{}", "FALSE"),
            Self::Atom { predicate, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", predicate.to_string(), ts.join(", "))
            }
            Self::Equals { left, right } => write!(f, "{} = {}", left, right),
            Self::Not { formula } => {
                match formula.as_ref() {
                    Self::Top | Self::Bottom | Self::Atom { .. } => write!(f, "~{}", formula),
                    _ => write!(f, "~({:?})", formula)
                }
            }
            Self::And { left, right } => {
                write_binary(left, right, "&", f)
            }
            Self::Or { left, right } => {
                write_binary(left, right, "|", f)
            }
            Self::Implies { left, right } => {
                write_binary(left, right, "->", f)
            }
            Self::Iff { left, right } => {
                write_binary(left, right, "<=>", f)
            }
            Self::Exists { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                match formula.as_ref() {
                    Self::Top | Self::Bottom | Self::Atom { .. } => {
                        write!(f, "? {}. {:?}", vs.join(", "), formula)
                    }
                    _ => {
                        write!(f, "? {}. ({:?})", vs.join(", "), formula)
                    }
                }
            }
            Self::Forall { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                match formula.as_ref() {
                    Self::Top | Self::Bottom | Self::Atom { .. } => {
                        write!(f, "! {}. {:?}", vs.join(", "), formula)
                    }
                    _ => {
                        write!(f, "! {}. ({:?})", vs.join(", "), formula)
                    }
                }
            }
        }
    }
}

/// Is a first-order theory, containing a set of first-order formulae.
pub struct Theory {
    /// Is the list of first-order formulae in this theory.
    pub formulae: Vec<Formula>
}

impl From<Vec<Formula>> for Theory {
    fn from(formulae: Vec<Formula>) -> Self {
        Theory { formulae }
    }
}

impl fmt::Display for Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let fs: Vec<String> = self.formulae.iter().map(|t| t.to_string()).collect();
        write!(f, "{}", fs.join("\n"))
    }
}

//// Tests -------------------------------------
#[cfg(test)]
mod test_syntax {
    use super::*;
    use super::Formula::*;
    use crate::test_prelude::*;

    #[test]
    fn test_var_to_string() {
        assert_eq!("x", x().to_string());
        assert_eq!("y", y().to_string());
    }

    #[test]
    fn test_var_free_vars() {
        assert_eq_vectors(&vec![&V("x".to_owned())], &x().free_vars());
    }

    #[test]
    fn test_func_to_string() {
        assert_eq!("f", f().to_string());
        assert_eq!("g", g().to_string());
    }

    #[test]
    fn test_const_to_string() {
        assert_eq!("'a", a().to_string());
        assert_eq!("'b", b().to_string());
    }

    #[test]
    fn test_const_free_vars() {
        let expected: Vec<&V> = Vec::new();
        assert_eq_vectors(&expected, &a().free_vars());
    }

    #[test]
    fn test_app_to_string() {
        let term_0: Term = f().app0();
        assert_eq!("f()", term_0.to_string());
        assert_eq!("f(x, y)", f().app2(x(), y()).to_string());
        assert_eq!("f(g(x), y)", f().app2(g().app1(x()), y()).to_string());
        {
            assert_eq!("f(f(f(f(f(f(f(x)))))))",
                       f().app1(
                           f().app1(
                               f().app1(
                                   f().app1(
                                       f().app1(
                                           f().app1(
                                               f().app1(x())
                                           )
                                       )
                                   )
                               )
                           )
                       ).to_string());
        }
    }

    #[test]
    fn test_app_free_vars() {
        {
            let term_0: Term = f().app0();
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &term_0.free_vars());
        }
        {
            let g_0: Term = g().app0();
            let h_0: Term = g().app0();
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected,
                              &f().app1(
                                  g().app2(
                                      h_0, g_0,
                                  )
                              ).free_vars());
        }
        {
            let vars = vec![_x()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &f().app1(x()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &f().app3(x(), y(), z()).free_vars());
        }
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &f().app3(x(), y(), x()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected,
                              &f().app2(
                                  g().app1(x()),
                                  h().app2(
                                      y(),
                                      f().app1(
                                          g().app1(z())
                                      ),
                                  ),
                              ).free_vars());
        }
    }

    #[test]
    fn test_pred_to_string() {
        assert_eq!("P", P().to_string());
        assert_eq!("Q", Q().to_string());
    }

    #[test]
    fn print_top() {
        assert_eq!("⊤", Top.to_string());
    }

    #[test]
    fn free_vars_top() {
        let expected: Vec<&V> = vec![];
        assert_eq!(expected, Top.free_vars());
    }

    #[test]
    fn print_bottom() {
        assert_eq!("⟘", Bottom.to_string());
    }

    #[test]
    fn free_vars_bottom() {
        let expected: Vec<&V> = vec![];
        assert_eq_vectors(&expected, &Bottom.free_vars());
    }

    #[test]
    fn test_atom_to_string() {
        assert_eq!("R()", R().app0().to_string());
        assert_eq!("R(x, y)", R().app2(x(), y()).to_string());
        assert_eq!("R(g(x, y))", R().app1(g().app2(x(), y())).to_string());
        {
            assert_eq!("R(f(f(f(f(f(f(x)))))))",
                       R().app1(
                           f().app1(
                               f().app1(
                                   f().app1(
                                       f().app1(
                                           f().app1(
                                               f().app1(x())
                                           )
                                       )
                                   )
                               )
                           )
                       ).to_string());
        }
    }

    #[test]
    fn test_atom_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &R().app0().free_vars());
        }
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &R().app2(x(), y()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &R().app2(
                y(),
                g().app2(x(), z()),
            ).free_vars());
        }
        {
            let vars = vec![_x(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected,
                              &R().app2(
                                  z(),
                                  f().app1(
                                      f().app1(
                                          f().app1(
                                              f().app1(
                                                  f().app1(
                                                      f().app1(x())
                                                  )
                                              )
                                          )
                                      )
                                  ),
                              ).free_vars());
        }
    }

    #[test]
    fn test_equals_to_string() {
        assert_eq!("x = y", x().equals(y()).to_string());
    }

    #[test]
    fn test_equals_free_vars() {
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &x().equals(y()).free_vars());
        }
        {
            let vars = vec![_x()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &x().equals(g().app0()).free_vars());
        }
    }

    #[test]
    fn test_not_to_string() {
        assert_eq!("¬R()", not(R().app0()).to_string());
        assert_eq!("¬(¬R())", not(not(R().app0())).to_string());
        assert_eq!("¬(x = y)", not(x().equals(y())).to_string());
        assert_eq!("¬R(x, y)", not(R().app2(x(), y())).to_string());
        assert_eq!("¬(R(x, y) ∧ Q(z))",
                   not(R().app2(x(), y()).and(Q().app1(z()))).to_string());
        assert_eq!("¬(R(x, y) ∨ Q(z))",
                   not(R().app2(x(), y()).or(Q().app1(z()))).to_string());
        assert_eq!("¬(R(x, y) ∧ (¬Q(z)))",
                   not(R().app2(x(), y()).and(not(Q().app1(z())))).to_string());
        assert_eq!("¬(R(x, y) → Q(z))",
                   not(R().app2(x(), y()).implies(Q().app1(z()))).to_string());
        assert_eq!("¬(R(x, y) ⇔ Q(z))",
                   not(R().app2(x(), y()).iff(Q().app1(z()))).to_string());
    }

    #[test]
    fn test_not_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &not(R().app0()).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &not(not(R().app0())).free_vars());
        }
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &not(x().equals(y())).free_vars());
        }
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &not(R().app2(x(), y())).free_vars());
        }
    }

    #[test]
    fn test_and_to_string() {
        assert_eq!("P() ∧ Q()", P().app0().and(Q().app0()).to_string());
        assert_eq!("P() ∧ (x = y)", P().app0().and(x().equals(y())).to_string());
        assert_eq!("P() ∧ (¬Q())", P().app0().and(not(Q().app0())).to_string());
        assert_eq!("P() ∧ (Q() ∧ R())", P().app0().and(Q().app0().and(R().app0())).to_string());
        assert_eq!("P() ∧ (Q() ∨ R())", P().app0().and(Q().app0().or(R().app0())).to_string());
        assert_eq!("P() ∧ (Q() → R())", P().app0().and(Q().app0().implies(R().app0())).to_string());
        assert_eq!("P() ∧ (Q() ⇔ R())", P().app0().and(Q().app0().iff(R().app0())).to_string());
    }

    #[test]
    fn test_and_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &P().app0().and(Q().app0()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &P().app2(z(), y()).and(x().equals(y())).free_vars());
        }
    }

    #[test]
    fn test_or_to_string() {
        assert_eq!("P() ∨ Q()", P().app0().or(Q().app0()).to_string());
        assert_eq!("P() ∨ (x = y)", P().app0().or(x().equals(y())).to_string());
        assert_eq!("P() ∨ (¬Q())", P().app0().or(not(Q().app0())).to_string());
        assert_eq!("P() ∨ (Q() ∧ R())", P().app0().or(Q().app0().and(R().app0())).to_string());
        assert_eq!("P() ∨ (Q() ∨ R())", P().app0().or(Q().app0().or(R().app0())).to_string());
        assert_eq!("P() ∨ (Q() → R())", P().app0().or(Q().app0().implies(R().app0())).to_string());
        assert_eq!("P() ∨ (Q() ⇔ R())", P().app0().or(Q().app0().iff(R().app0())).to_string());
    }

    #[test]
    fn test_or_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &P().app0().or(Q().app0()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &P().app2(z(), y()).or(x().equals(y())).free_vars());
        }
    }

    #[test]
    fn test_implies_to_string() {
        assert_eq!("P() → Q()", P().app0().implies(Q().app0()).to_string());
        assert_eq!("P() → (x = y)", P().app0().implies(x().equals(y())).to_string());
        assert_eq!("P() → (¬Q())", P().app0().implies(not(Q().app0())).to_string());
        assert_eq!("P() → (Q() ∧ R())", P().app0().implies(Q().app0().and(R().app0())).to_string());
        assert_eq!("P() → (Q() ∨ R())", P().app0().implies(Q().app0().or(R().app0())).to_string());
        assert_eq!("P() → (Q() → R())", P().app0().implies(Q().app0().implies(R().app0())).to_string());
        assert_eq!("P() → (Q() ⇔ R())", P().app0().implies(Q().app0().iff(R().app0())).to_string());
    }

    #[test]
    fn test_implies_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &P().app0().implies(Q().app0()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &P().app2(z(), y()).implies(x().equals(y())).free_vars());
        }
    }

    #[test]
    fn test_iff_to_string() {
        assert_eq!("P() ⇔ Q()", P().app0().iff(Q().app0()).to_string());
        assert_eq!("P() ⇔ (x = y)", P().app0().iff(x().equals(y())).to_string());
        assert_eq!("P() ⇔ (¬Q())", P().app0().iff(not(Q().app0())).to_string());
        assert_eq!("P() ⇔ (Q() ∧ R())", P().app0().iff(Q().app0().and(R().app0())).to_string());
        assert_eq!("P() ⇔ (Q() ∨ R())", P().app0().iff(Q().app0().or(R().app0())).to_string());
        assert_eq!("P() ⇔ (Q() → R())", P().app0().iff(Q().app0().implies(R().app0())).to_string());
        assert_eq!("P() ⇔ (Q() ⇔ R())", P().app0().iff(Q().app0().iff(R().app0())).to_string());
    }

    #[test]
    fn test_iff_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &P().app0().iff(Q().app0()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &P().app2(z(), y()).iff(x().equals(y())).free_vars());
        }
    }

    #[test]
    fn test_exists_to_string() {
        assert_eq!("∃ x. P(x)", exists1(_x(), P().app1(x())).to_string());
        assert_eq!("∃ x, y. P(x, y)", exists2(_x(), _y(), P().app2(x(), y())).to_string());
        assert_eq!("∃ x, y. (x = y)", exists2(_x(), _y(), x().equals(y())).to_string());
        assert_eq!("∃ x. (¬Q(x))", exists1(_x(), not(Q().app1(x()))).to_string());
        assert_eq!("∃ x. (Q(x) ∧ R(x))", exists1(_x(), Q().app1(x()).and(R().app1(x()))).to_string());
        assert_eq!("∃ x. (Q(x) ∨ R(x))", exists1(_x(), Q().app1(x()).or(R().app1(x()))).to_string());
        assert_eq!("∃ x. (Q(x) → R(x))", exists1(_x(), Q().app1(x()).implies(R().app1(x()))).to_string());
        assert_eq!("∃ x. (Q(x) ⇔ R(x))", exists1(_x(), Q().app1(x()).iff(R().app1(x()))).to_string());
    }

    #[test]
    fn test_exists_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &exists1(_x(), P().app1(x())).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &exists2(_x(), _y(), P().app2(x(), y())).free_vars());
        }
        {
            let vars = vec![_y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &exists1(_x(), x().equals(y())).free_vars());
        }
        {
            let vars = vec![_y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &exists1(_x(), Q().app1(x()).and(R().app1(y()))).free_vars());
        }
        {
            let vars = vec![_y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &exists1(_x(), Q().app2(x(), z()).and(R().app2(x(), y()))).free_vars());
        }
    }

    #[test]
    fn test_forall_to_string() {
        assert_eq!("∀ x. P(x)", forall1(_x(), P().app1(x())).to_string());
        assert_eq!("∀ x, y. P(x, y)", forall2(_x(), _y(), P().app2(x(), y())).to_string());
        assert_eq!("∀ x, y. (x = y)", forall2(_x(), _y(), x().equals(y())).to_string());
        assert_eq!("∀ x. (¬Q(x))", forall1(_x(), not(Q().app1(x()))).to_string());
        assert_eq!("∀ x. (Q(x) ∧ R(x))", forall1(_x(), Q().app1(x()).and(R().app1(x()))).to_string());
        assert_eq!("∀ x. (Q(x) ∨ R(x))", forall1(_x(), Q().app1(x()).or(R().app1(x()))).to_string());
        assert_eq!("∀ x. (Q(x) → R(x))", forall1(_x(), Q().app1(x()).implies(R().app1(x()))).to_string());
        assert_eq!("∀ x. (Q(x) ⇔ R(x))", forall1(_x(), Q().app1(x()).iff(R().app1(x()))).to_string());
    }

    #[test]
    fn test_forall_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &forall1(_x(), P().app1(x())).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &forall2(_x(), _y(), P().app2(x(), y())).free_vars());
        }
        {
            let vars = vec![_y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &forall1(_x(), x().equals(y())).free_vars());
        }
        {
            let vars = vec![_y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &forall1(_x(), Q().app1(x()).and(R().app1(y()))).free_vars());
        }
        {
            let vars = vec![_y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &forall1(_x(), Q().app2(x(), z()).and(R().app2(x(), y()))).free_vars());
        }
    }

    #[test]
    fn test_formula_to_string() {
        let expected = "∀ x. (x = x)\n\
            ∀ x, y. ((x = y) → (y = x))\n\
        ∀ x, y, z. (((x = y) ∧ (y = z)) → (x = z))";
        let theory = Theory::from(vec![
            forall1(_x(), x().equals(x())),
            forall2(_x(), _y(), x().equals(y()).implies(y().equals(x()))),
            forall3(_x(), _y(), _z(), x().equals(y()).and(y().equals(z())).implies(x().equals(z()))),
        ]);
        assert_eq!(expected, theory.to_string());
    }
}