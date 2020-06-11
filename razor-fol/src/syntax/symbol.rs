/*! Defines the symbols consisting of ['V'], ['C'], ['F'] and ['Pred'] for making terms and formulae.

['V']: ./struct.V.html
['C']: ./struct.C.html
['F']: ./struct.F.html
['Pred']: ./struct.Pred.html
*/

use super::{Formula, Term};
use std::fmt;

/// Represents an uninterpreted function symbol with a given name.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F(pub String);

impl F {
    /// Applies the receiver on a list of terms. The length of `terms` must be equal to
    /// the (assumed) arity of the function.
    ///
    /// **Note**: the definition of [`F`] does not impose any restrictions on the
    /// arity of function symbols. The user is expected to assume the arity of the function.
    ///
    /// [`F`]: ./struct.F.html
    pub fn app<T: FApp>(self, args: Vec<T>) -> T {
        T::apply(self, args)
    }

    /// Applies the (nullary) function.
    pub fn app0<T: FApp>(self) -> T {
        T::apply(self, vec![])
    }

    /// Applies the (unary) receiver on an argument.
    pub fn app1<T: FApp>(self, first: T) -> T {
        T::apply(self, vec![first])
    }

    /// Applies the (binary) receiver on two arguments.
    pub fn app2<T: FApp>(self, first: T, second: T) -> T {
        T::apply(self, vec![first, second])
    }

    /// Applies the (ternary) receiver on three arguments.
    pub fn app3<T: FApp>(self, first: T, second: T, third: T) -> T {
        T::apply(self, vec![first, second, third])
    }

    /// Applies the (4-ary) receiver on four arguments.
    pub fn app4<T: FApp>(self, first: T, second: T, third: T, fourth: T) -> T {
        T::apply(self, vec![first, second, third, fourth])
    }

    /// Applies the (5-ary) receiver on five arguments.
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
///
pub trait FApp: Sized {
    /// Builds a composite term by applying `function` on `args` as arguments.
    fn apply(function: F, args: Vec<Self>) -> Self;
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
pub struct C(pub String);

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
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Pred(pub String);

impl Pred {
    /// Applies the receiver on a list of arguments. The length of `terms` must be equal to
    /// the (assumed) arity of the predicate.
    ///
    /// **Note**: the definition of [`Pred`] does not impose any restrictions
    /// on the arity of predicate symbols. The user is expected to assume the arity of the predicate.
    ///
    /// [`Pred`]: ./struct.Pred.html
    pub fn app(self, terms: Vec<Term>) -> Formula {
        Formula::Atom {
            predicate: self,
            terms,
        }
    }

    /// Applies the (nullary) receiver.
    pub fn app0(self) -> Formula {
        Formula::Atom {
            predicate: self,
            terms: vec![],
        }
    }

    /// Applies the (unary) receiver on a term.
    pub fn app1(self, first: Term) -> Formula {
        Formula::Atom {
            predicate: self,
            terms: vec![first],
        }
    }

    /// Applies the (binary) receiver on two terms.
    pub fn app2(self, first: Term, second: Term) -> Formula {
        Formula::Atom {
            predicate: self,
            terms: vec![first, second],
        }
    }

    /// Applies the (ternary) receiver on three terms.
    pub fn app3(self, first: Term, second: Term, third: Term) -> Formula {
        Formula::Atom {
            predicate: self,
            terms: vec![first, second, third],
        }
    }

    /// Applies the (4-ary) receiver on four terms.
    pub fn app4(self, first: Term, second: Term, third: Term, fourth: Term) -> Formula {
        Formula::Atom {
            predicate: self,
            terms: vec![first, second, third, fourth],
        }
    }

    /// Applies the (5-ary) receiver on five terms.
    pub fn app5(
        self,
        first: Term,
        second: Term,
        third: Term,
        fourth: Term,
        fifth: Term,
    ) -> Formula {
        Formula::Atom {
            predicate: self,
            terms: vec![first, second, third, fourth, fifth],
        }
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

#[cfg(test)]
mod tests {
    use super::*;
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
    fn test_pred_to_string() {
        assert_eq!("P", P().to_string());
        assert_eq!("Q", Q().to_string());
    }
}
