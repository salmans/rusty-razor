use itertools::Itertools;

use std::fmt;

/// ## Syntactic Symbols
pub trait Symbol {}

/// ## Function
/// Represents function symbols.
pub struct Func {
    pub name: String,
}

impl Func {
    pub fn new(name: &str) -> Func {
        Func { name: name.to_string() }
    }

    pub fn app(self, terms: Terms) -> Term {
        Term::App { function: self, terms }
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

/// ## Variable
/// Represents variable symbols.
#[derive(PartialEq, Eq, Hash)]
pub struct V(String);

impl V {
    pub fn new(name: &str) -> V {
        V(name.to_string())
    }
}

impl fmt::Display for V {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl Symbol for V {}

/// ## Constant
/// Represents constant symbols.
#[derive(PartialEq, Eq, Hash)]
pub struct C(String);

impl C {
    pub fn new(name: &str) -> C {
        C(name.to_string())
    }
}

impl fmt::Display for C {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl Symbol for C {}

/// ## Term
pub enum Term {
    /// ### Variable
    /// Represents a variable term; e.g., `x`.
    Var { variable: V },

    /// ### Constant
    /// Represents a constant term; e.g., `'c`.
    /// > **Note:** Although constants are technically zero arity functions, we distinguish constants and functions syntactically.
    Const { constant: C },

    /// ### Function Application
    /// Represents a complex term, made by applying a function to a list of terms; e.g., `f(x,y)`
    App { function: Func, terms: Vec<Term> },
}

impl Term {
    pub fn var(name: &str) -> Term {
        Term::Var { variable: V::new(name) }
    }

    pub fn r#const(name: &str) -> Term {
        Term::Const { constant: C::new(name) }
    }

    /// Returns a list of free variables in the term.
    /// * For efficiency reasons, the function returns references to the free variables in the term but it
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
}

type Terms = Vec<Term>;

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Term::Var { variable } => write!(f, "{}", variable.0),
            Term::Const { constant } => write!(f, "'{}", constant.0),
            Term::App { function, terms } => {
                let strs: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", function.to_string(), strs.join(", "))
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

//// Tests -------------------------------------
#[cfg(test)]
mod test_syntax {
    use super::*;
    use crate::test_prelude::*;

    #[test]
    fn test_var_to_string() {
        assert_eq!("x", x().to_string());
        assert_eq!("y", y().to_string());
    }

    #[test]
    fn test_var_free_vars() {
        assert_eq!(vec![&V("x".to_string())], x().free_vars());
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
        assert_eq!(expected, a().free_vars());
    }

    #[test]
    fn test_app_to_string() {
        assert_eq!("f()", f().app(vec![]).to_string());
        assert_eq!("f(x, y)", f().app(vec![x(), y()]).to_string());
        assert_eq!("f(g(x, y))", f().app(vec![g().app(vec![x(), y()])]).to_string());
        {
            assert_eq!("f(f(f(f(f(f(f(x)))))))",
                       f().app(vec![
                           f().app(vec![
                               f().app(vec![
                                   f().app(vec![
                                       f().app(vec![
                                           f().app(vec![
                                               f().app(vec![x()])
                                           ])
                                       ])
                                   ])
                               ])
                           ])
                       ]).to_string());
        }
    }

    #[test]
    fn test_app_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq!(expected, f().app(vec![]).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq!(expected,
                       f().app(vec![
                           g().app(vec![
                               h().app(vec![]), g().app(vec![])
                           ])
                       ]).free_vars());
        }
        {
            let v_x = V::new("x");
            let expected: Vec<&V> = vec![&v_x];
            assert_eq!(expected, f().app(vec![x()]).free_vars());
        }
        {
            let vars = vec![V::new("x"), V::new("y"), V::new("z")];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq!(expected, f().app(vec![x(), y(), z()]).free_vars());
        }
        {
            let vars = vec![V::new("x"), V::new("y")];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq!(expected, f().app(vec![x(), y(), x()]).free_vars());
        }
        {
            let vars = vec![V::new("x"), V::new("y"), V::new("z")];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq!(expected,
                       f().app(vec![
                           g().app(vec![x()]),
                           h().app(vec![
                               y(),
                               f().app(vec![
                                   g().app(vec![z()])
                               ])
                           ])
                       ]).free_vars());
        }
    }
}