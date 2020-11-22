/*! Defines the syntax for first-order terms. */

use super::{FApp, C, F, FOF, V};
use std::fmt;

/// Represents a first-order term and consists of variables, constants and function applications.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    /// Is a variable term, wrapping a [variable symbol].
    ///
    /// [variable symbol]: crate::syntax::V
    Var { variable: V },

    /// Is a constant term, wrapping a [constant symbol].
    ///
    /// [constant symbol]: crate::syntax::C
    Const { constant: C },

    /// Is a composite term, made by applying a `function` on a list of `terms`.
    App { function: F, terms: Vec<Term> },
}

impl Term {
    /// Returns a list of all free variable symbols in the term.
    ///
    /// **Note**: In the list of free variables, each variable symbol appears only once even if it
    /// is present at multiple positions of the receiver term.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::{syntax::{V, C, F, Term}, term};
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
    /// let t = term!(f(x, g(y, @c, x)));
    ///
    /// // comparing the two (unordered) lists:
    /// assert_eq!(vec![&x_sym, &y_sym].iter().sorted(), t.free_vars().iter().sorted())
    /// ```
    pub fn free_vars(&self) -> Vec<&V> {
        use itertools::Itertools;

        match self {
            Term::Var { variable } => vec![variable],
            Term::Const { constant: _ } => vec![],
            Term::App { function: _, terms } => terms
                .iter()
                .flat_map(|t| t.free_vars())
                .into_iter()
                .unique()
                .collect(),
        }
    }

    /// Returns an [equation] (formula) between the receiver and `term`.
    ///
    /// [equation]: crate::syntax::FOF::Equals
    ///
    pub fn equals(self, term: Term) -> FOF {
        FOF::Equals {
            left: self,
            right: term,
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term;
    use crate::{assert_eq_sorted_vecs, v};

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
