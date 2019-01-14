use itertools::Itertools;

use std::fmt;

/// ## Syntactic Symbols
pub trait Symbol {}

/// ### Function
/// Function symbols.
#[derive(Clone)]
pub struct Func {
    pub name: String,
}

impl Func {
    pub fn new(name: &str) -> Func {
        Func { name: name.to_string() }
    }
    /// Applies the function to a list of terms.
    pub fn app(self, terms: Terms) -> Term {
        Term::App { function: self, terms }
    }
    /// Applies the function to a list of terms.
    pub fn app0(self) -> Term {
        Term::App { function: self, terms: vec![] }
    }
    /// Applies the (unary) function to a term.
    pub fn app1(self, first: Term) -> Term {
        Term::App { function: self, terms: vec![first] }
    }
    /// Applies the (binary) predicate to two terms.
    pub fn app2(self, first: Term, second: Term) -> Term {
        Term::App { function: self, terms: vec![first, second] }
    }
    /// Applies the (ternary) function to three terms.
    pub fn app3(self, first: Term, second: Term, third: Term) -> Term {
        Term::App { function: self, terms: vec![first, second, third] }
    }
    /// Applies the (4-ary) function to four terms.
    pub fn app4(self, first: Term, second: Term, third: Term, fourth: Term) -> Term {
        Term::App { function: self, terms: vec![first, second, third, fourth] }
    }
    /// Applies the (5-ary) function to five terms.
    pub fn app5(self, first: Term, second: Term, third: Term, fourth: Term, fifth: Term) -> Term {
        Term::App { function: self, terms: vec![first, second, third, fourth, fifth] }
    }
}

impl fmt::Display for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.name)
    }
}

impl PartialEq for Func {
    fn eq(&self, other: &Func) -> bool {
        self.name == other.name
    }
}

impl Symbol for Func {}

/// ### Variable
/// Variable symbols.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct V(pub String);

impl V {
    pub fn new(name: &str) -> V {
        V(name.to_string())
    }

    pub fn var(self) -> Term {
        Term::Var { variable: self }
    }
}

impl fmt::Display for V {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl Symbol for V {}

/// ### Constant
/// Constant symbols.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct C(String);

impl C {
    pub fn new(name: &str) -> C {
        C(name.to_string())
    }

    pub fn r#const(self) -> Term {
        Term::Const { constant: self }
    }
}

impl fmt::Display for C {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl Symbol for C {}

/// ### Predicate
/// Predicate symbols.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Pred(String);

impl Pred {
    pub fn new(name: &str) -> Pred {
        Pred(name.to_string())
    }
    /// Applies the predicate to a list of terms.
    pub fn app(self, terms: Terms) -> Formula {
        Formula::Atom { predicate: self, terms }
    }
    /// Applies the predicate to a list of terms.
    pub fn app0(self) -> Formula {
        Formula::Atom { predicate: self, terms: vec![] }
    }
    /// Applies the (unary) predicate to a term.
    pub fn app1(self, first: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first] }
    }
    /// Applies the (binary) predicate to two terms.
    pub fn app2(self, first: Term, second: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first, second] }
    }
    /// Applies the (ternary) predicate to three terms.
    pub fn app3(self, first: Term, second: Term, third: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first, second, third] }
    }
    /// Applies the (4-ary) predicate to four terms.
    pub fn app4(self, first: Term, second: Term, third: Term, fourth: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first, second, third, fourth] }
    }
    /// Applies the (5-ary) predicate to five terms.
    pub fn app5(self, first: Term, second: Term, third: Term, fourth: Term, fifth: Term) -> Formula {
        Formula::Atom { predicate: self, terms: vec![first, second, third, fourth, fifth] }
    }
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl Symbol for Pred {}

/// ## Term
#[derive(Clone)]
pub enum Term {
    /// ### Variable
    /// Variable term; e.g., `x`.
    Var { variable: V },

    /// ### Constant
    /// Constant term; e.g., `'c`.
    /// > **Note:** Although constants are technically zero arity functions, we distinguish constants and functions syntactically.
    Const { constant: C },

    /// ### Function Application
    /// Complex term, made by applying a function to a list of terms; e.g., `f(x, y)`
    App { function: Func, terms: Vec<Term> },
}

impl Term {
    pub fn r#const(name: &str) -> Term {
        Term::Const { constant: C::new(name) }
    }

    // TODO make free_vars lazy
    /// Returns a list of free variables in the term.
    /// * For efficiency reasons, `free_vars` returns references to the free variables in the term but it
    /// is supposed to eliminate duplicate variables.
    pub fn free_vars(&self) -> Vec<&V> {
        match self {
            Term::Var { variable } => vec![variable],
            Term::Const { constant: _ } => vec![],
            Term::App { function: _, terms } => {
                terms.iter().flat_map(|t| t.free_vars()).into_iter().unique().collect()
            }
        }
    }

    pub fn equals(self, rhs: Term) -> Formula {
        Formula::Equals { left: self, right: rhs }
    }
}

pub type Terms = Vec<Term>;

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Term::Var { variable } => write!(f, "{}", variable.0),
            Term::Const { constant } => write!(f, "'{}", constant.0),
            Term::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", function, ts.join(", "))
            }
        }
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var { variable: v1 }, Term::Var { variable: v2 }) => v1 == v2,
            (Term::Const { constant: c1 }, Term::Const { constant: c2 }) => c1 == c2,
            (Term::App { function: f1, terms: ts1 }, Term::App { function: f2, terms: ts2 }) => {
                f1 == f2 && ts1.iter().zip(ts2).all(|(x, y)| x == y)
            }
            _ => false
        }
    }
}

/// ## Formula
/// A first order formula.
#[derive(Clone)]
pub enum Formula {
    /// ### Top
    /// Top (⊤) or Turth
    Top,

    /// ### Bottom
    /// Bottom (⟘) or Falsehood
    Bottom,

    /// ### Atomic Formula
    /// Atomic formula, made by applying a predicate on a list of terms; e.g., `P(x, f(y), 'c)`.
    Atom { predicate: Pred, terms: Vec<Term> },

    /// ### Equality
    /// Equality among two terms is a special kind of atomic formula; e.g., `f(x) = 'c`.
    Equals { left: Term, right: Term },

    /// ### Negation
    /// Not `formula`; e.g., ¬R(x).
    Not { formula: Box<Formula> },

    /// ### Conjunction
    /// `left` and `right`; e.g., R(x) ∧ Q(y).
    And { left: Box<Formula>, right: Box<Formula> },

    /// ### Disjunction
    /// `left` or `right`; e.g., R(x) ∨ Q(y).
    Or { left: Box<Formula>, right: Box<Formula> },

    /// ### Implication
    /// `left` implies `right`; e.g., P(x) → Q(x).
    Implies { left: Box<Formula>, right: Box<Formula> },

    /// ### Bi-Implication
    /// `left` if and only if `right`; e.g., P(x) ⇔ Q(x).
    Iff { left: Box<Formula>, right: Box<Formula> },

    /// ### Existential Formula
    /// Exists `variables` such that `formula` is true; e.g., ∃ x.P(x).
    Exists { variables: Vec<V>, formula: Box<Formula> },

    /// ### Universal Formula
    /// For all `variables`, `formula` is true; e.g., ∀ x.P(x).
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

/// Returns an existentially quantified formula with a variable and `formula`.
pub fn exists1(first: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first], formula: Box::new(formula) }
}

/// Returns an existentially quantified formula with two variables and `formula`.
pub fn exists2(first: V, second: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first, second], formula: Box::new(formula) }
}

/// Returns an existentially quantified formula with three variables and `formula`.
pub fn exists3(first: V, second: V, third: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first, second, third], formula: Box::new(formula) }
}

/// Returns an existentially quantified formula with four variables and `formula`.
pub fn exists4(first: V, second: V, third: V, fourth: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first, second, third, fourth], formula: Box::new(formula) }
}

/// Returns an existentially quantified formula with four variables and `formula`.
pub fn exists5(first: V, second: V, third: V, fourth: V, fifth: V, formula: Formula) -> Formula {
    Formula::Exists { variables: vec![first, second, third, fourth, fifth], formula: Box::new(formula) }
}

/// Returns a universally quantified formula with the given `variables` and `formula`.
pub fn forall(variables: Vec<V>, formula: Formula) -> Formula {
    Formula::Forall { variables, formula: Box::new(formula) }
}

/// Returns a universally quantified formula with a variable and `formula`.
pub fn forall1(first: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first], formula: Box::new(formula) }
}

/// Returns a universally quantified formula with two variables and `formula`.
pub fn forall2(first: V, second: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first, second], formula: Box::new(formula) }
}

/// Returns a universally quantified formula with three variables and `formula`.
pub fn forall3(first: V, second: V, third: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first, second, third], formula: Box::new(formula) }
}

/// Returns a universally quantified formula with four variables and `formula`.
pub fn forall4(first: V, second: V, third: V, fourth: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first, second, third, fourth], formula: Box::new(formula) }
}

/// Returns a universally quantified formula with four variables and `formula`.
pub fn forall5(first: V, second: V, third: V, fourth: V, fifth: V, formula: Formula) -> Formula {
    Formula::Forall { variables: vec![first, second, third, fourth, fifth], formula: Box::new(formula) }
}

impl Formula {
    /// Returns the result of the conjunction between this formula and `formula`.
    pub fn and(self, formula: Formula) -> Formula {
        Formula::And { left: Box::new(self), right: Box::new(formula) }
    }

    /// Returns the result of the disjunction between this formula and `formula`.
    pub fn or(self, formula: Formula) -> Formula {
        Formula::Or { left: Box::new(self), right: Box::new(formula) }
    }

    /// Returns the result of the implication between this formula and `formula`.
    pub fn implies(self, formula: Formula) -> Formula {
        Formula::Implies { left: Box::new(self), right: Box::new(formula) }
    }

    /// Returns the result of the bi-implication between this formula and `formula`.
    pub fn iff(self, formula: Formula) -> Formula {
        Formula::Iff { left: Box::new(self), right: Box::new(formula) }
    }

    // TODO make free_vars lazy
    /// Returns a list of free variables in the formula.
    /// * For efficiency reasons, `free_vars` returns references to the free variables in the term but it
    /// is supposed to eliminate duplicate variables.
    pub fn free_vars(&self) -> Vec<&V> {
        match self {
            Formula::Top => vec![],
            Formula::Bottom => vec![],
            Formula::Atom { predicate: _, terms } => {
                terms.iter().flat_map(|t| t.free_vars()).unique().collect()
            }
            Formula::Equals { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Formula::Not { formula } => formula.free_vars(),
            Formula::And { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Formula::Or { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Formula::Implies { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Formula::Iff { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Formula::Exists { variables, formula } => {
                formula.free_vars().into_iter().filter(|v| !variables.contains(v)).collect()
            }
            Formula::Forall { variables, formula } => {
                formula.free_vars().into_iter().filter(|v| !variables.contains(v)).collect()
            }
        }
    }
}

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
            Formula::Top => write!(f, "{}", "⊤"),
            Formula::Bottom => write!(f, "{}", "⟘"),
            Formula::Atom { predicate, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", predicate.to_string(), ts.join(", "))
            }
            Formula::Equals { left, right } => write!(f, "{} = {}", left, right),
            Formula::Not { formula } => write!(f, "¬{}", parens(formula)),
            Formula::And { left, right } => write!(f, "{} ∧ {}", parens(left), parens(right)),
            Formula::Or { left, right } => write!(f, "{} ∨ {}", parens(left), parens(right)),
            Formula::Implies { left, right } => write!(f, "{} → {}", parens(left), parens(right)),
            Formula::Iff { left, right } => write!(f, "{} ⇔ {}", parens(left), parens(right)),
            Formula::Exists { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                write!(f, "∃ {}. {}", vs.join(", "), parens(formula))
            }
            Formula::Forall { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                write!(f, "∀ {}. {}", vs.join(", "), parens(formula))
            }
        }
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Formula) -> bool {
        match (self, other) {
            (Formula::Top, Formula::Top) => true,
            (Formula::Bottom, Formula::Bottom) => true,
            (Formula::Atom { predicate: p1, terms: ts1 }, Formula::Atom { predicate: p2, terms: ts2 }) => {
                p1 == p2 && ts1.iter().zip(ts2).all(|(x, y)| x == y)
            },
            (Formula::Equals { left: l1, right: r1 }, Formula::Equals { left: l2, right: r2 }) => l1 == l2 && r1 == r2,
            (Formula::Not { formula: f1 }, Formula::Not { formula: f2 }) => f1 == f2,
            (Formula::And { left: l1, right: r1 }, Formula::And { left: l2, right: r2 }) => l1 == l2 && r1 == r2,
            (Formula::Or { left: l1, right: r1 }, Formula::Or { left: l2, right: r2 }) => l1 == l2 && r1 == r2,
            (Formula::Implies { left: l1, right: r1 }, Formula::Implies { left: l2, right: r2 }) => l1 == l2 && r1 == r2,
            (Formula::Iff { left: l1, right: r1 }, Formula::Iff { left: l2, right: r2 }) => l1 == l2 && r1 == r2,
            (Formula::Exists { variables: vs1, formula: f1 }, Formula::Exists { variables: vs2, formula: f2 }) => vs1 == vs2 && f1 == f2,
            (Formula::Forall { variables: vs1, formula: f1 }, Formula::Forall { variables: vs2, formula: f2 }) => vs1 == vs2 && f1 == f2,
            _ => false
        }
    }
}

/// ## Theory
/// A first-order theory is a set of first-order formulas.
pub struct Theory {
    pub formulas: Vec<Formula>
}

impl Theory {
    pub fn new(formulas: Vec<Formula>) -> Theory {
        Theory { formulas }
    }
}

impl fmt::Display for Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let fs: Vec<String> = self.formulas.iter().map(|t| t.to_string()).collect();
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
        assert_eq_vectors(&vec![&V("x".to_string())], &x().free_vars());
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
        assert_eq!("f()", f().app0().to_string());
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
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &f().app0().free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected,
                              &f().app1(
                                  g().app2(
                                      h().app0(), g().app0(),
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
        let theory = Theory::new(vec![
            forall1(_x(), x().equals(x())),
            forall2(_x(), _y(), x().equals(y()).implies(y().equals(x()))),
            forall3(_x(), _y(), _z(), x().equals(y()).and(y().equals(z())).implies(x().equals(z()))),
        ]);
        assert_eq!(expected, theory.to_string());
    }
}