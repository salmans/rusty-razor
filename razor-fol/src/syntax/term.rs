/*! Defines the syntax for first-order terms. */

use super::{formula::Equals, C, F, FOF, V};
use std::fmt;

/// Is the trait of types that act as terms.
pub trait Term {}

/// Represents a (complex) first-order term and consists of variables, constants and function applications.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Complex {
    /// Is a variable term, wrapping a [variable symbol].
    ///
    /// [variable symbol]: crate::syntax::V
    Var { variable: V },

    /// Is a constant term, wrapping a [constant symbol].
    ///
    /// [constant symbol]: crate::syntax::C
    Const { constant: C },

    /// Recursively defines a term by applying a `function` on a list of `terms`.
    App { function: F, terms: Vec<Complex> },
}

impl Complex {
    /// Returns an [equation] (formula) between the receiver and `term`.
    ///
    /// [equation]: crate::syntax::FOF::Equals
    ///
    pub fn equals(self, term: Self) -> FOF {
        Equals {
            left: self,
            right: term,
        }
        .into()
    }

    /// Builds a term by applying `function` on `args` as arguments.
    pub fn apply(function: F, terms: Vec<Self>) -> Self {
        Self::App { function, terms }
    }
}

impl Term for Complex {}

impl From<V> for Complex {
    fn from(variable: V) -> Self {
        Self::Var { variable }
    }
}

impl From<C> for Complex {
    fn from(constant: C) -> Self {
        Self::Const { constant }
    }
}

impl fmt::Display for Complex {
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

impl fmt::Debug for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_eq_sorted_vecs, term, transform::TermBased, v};

    #[test]
    fn test_var_free_vars() {
        let term = term!(x);
        let x = v!(x);
        assert_eq_sorted_vecs!(vec![&x], term.free_vars());
    }

    #[test]
    fn test_const_free_vars() {
        let expected: Vec<&V> = Vec::new();
        let fmla = term!(@a);
        assert_eq_sorted_vecs!(expected, fmla.free_vars());
    }

    #[test]
    fn test_app_to_string() {
        assert_eq!("f()", term!(f()).to_string());
        assert_eq!("f(x, y)", term!(f(x, y)).to_string());
        assert_eq!("f(g(x), y)", term!(f(g(x), y)).to_string());
        assert_eq!(
            "f(f(f(f(f(f(f(x)))))))",
            term!(f(f(f(f(f(f(f(x)))))))).to_string(),
        );
    }

    #[test]
    fn test_app_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            let fmla = term!(f());
            assert_eq_sorted_vecs!(expected, fmla.free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            let fmla = term!(f(g(h(), g())));
            assert_eq_sorted_vecs!(expected, fmla.free_vars());
        }
        {
            let expected = vec![v!(x)];
            let term = term!(f(x));
            assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), term.free_vars());
        }
        {
            let expected = [v!(x), v!(y), v!(z)];
            let term = term!(f(x, y, z));
            assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), term.free_vars());
        }
        {
            let expected = vec![v!(x), v!(y)];
            let term = term!(f(x, y, x));
            assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), term.free_vars());
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            let term = term!(f(g(x), h(y, f(g(z)))));
            assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), term.free_vars(),);
        }
    }
}
