/*! Defines the syntax for first-order terms. */

use super::{FApp, Formula, C, F, V};
use std::fmt;

/// Represents a first-order term and consists of variables, constants and function applications.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    /// Is a variable term, wrapping a [variable symbol].
    ///
    /// [variable symbol]: ./struct.V.html
    Var { variable: V },

    /// Is a constant term, wrapping a [constant symbol].
    ///
    /// [constant symbol]: ./struct.C.html
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
    /// # use razor_fol::syntax::{V, C, F, Term};
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
    /// [equation]: ./enum.Formula.html#variant.Equals
    ///
    pub fn equals(self, term: Term) -> Formula {
        Formula::Equals {
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
    use crate::test_prelude::*;

    #[test]
    fn test_app_to_string() {
        let term_0: Term = f().app0();
        assert_eq!("f()", term_0.to_string());
        assert_eq!("f(x, y)", f().app2(x(), y()).to_string());
        assert_eq!("f(g(x), y)", f().app2(g().app1(x()), y()).to_string());
        {
            assert_eq!(
                "f(f(f(f(f(f(f(x)))))))",
                f().app1(f().app1(f().app1(f().app1(f().app1(f().app1(f().app1(x())))))))
                    .to_string()
            );
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
            assert_eq_vectors(&expected, &f().app1(g().app2(h_0, g_0)).free_vars());
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
            assert_eq_vectors(
                &expected,
                &f().app2(g().app1(x()), h().app2(y(), f().app1(g().app1(z()))))
                    .free_vars(),
            );
        }
    }
}
