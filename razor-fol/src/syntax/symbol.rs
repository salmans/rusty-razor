/*! Defines the symbols of ['Var'], ['Const'], ['Func'] and ['Pred'] for making terms
and formulae.

['Var']: crate::syntax::Var
['Const']: crate::syntax::Const
['Func']: crate::syntax::Func
['Pred']: crate::syntax::Pred
*/

use super::{formula::Atom, term::Complex, FOF};
use std::fmt;

/// Represents an uninterpreted function symbol with a given name.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Func(String);

impl Func {
    /// Returns the function name.
    #[inline(always)]
    pub fn name(&self) -> &str {
        &self.0
    }

    /// Applies the receiver on a list of terms. The length of `terms` must be equal to
    /// the (assumed) arity of the function.
    ///
    /// **Note**: the definition of [`Func`] does not impose any restrictions on the
    /// arity of function symbols. The user is expected to assume the arity of the function.
    ///
    /// [`Func`]: crate::syntax::Func
    pub fn app(self, args: Vec<Complex>) -> Complex {
        Complex::apply(self, args)
    }
}

impl<S: Into<String>> From<S> for Func {
    fn from(name: S) -> Self {
        Self(name.into())
    }
}

impl fmt::Display for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Represents a variable symbol with a given name.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Var(String);

impl Var {
    /// Returns the variable name.
    #[inline(always)]
    pub fn name(&self) -> &str {
        &self.0
    }
}

impl<S: Into<String>> From<S> for Var {
    fn from(name: S) -> Self {
        Self(name.into())
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Represents a constant symbol with a given name.
///
/// **Note**: Although it is possible to treat nullary functions as constants, we distinguish
/// the two at a syntactic level.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Const(String);

impl Const {
    /// Returns the constant name.
    #[inline(always)]
    pub fn name(&self) -> &str {
        &self.0
    }
}

impl<S: Into<String>> From<S> for Const {
    fn from(name: S) -> Self {
        Self(name.into())
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "'{}", self.0)
    }
}

impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Represents a predicate symbol with a given name.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Pred(String);

impl Pred {
    /// Returns the predicate name.
    #[inline(always)]
    pub fn name(&self) -> &str {
        &self.0
    }

    /// Applies the receiver on a list of arguments. The length of `terms` must be equal to
    /// the (assumed) arity of the predicate.
    ///
    /// **Note**: the definition of [`Pred`] does not impose any restrictions
    /// on the arity of predicate symbols. The user is expected to assume the arity of the predicate.
    ///
    /// [`Pred`]: crate::syntax::Pred
    pub fn app(self, terms: Vec<Complex>) -> FOF {
        Atom {
            predicate: self,
            terms,
        }
        .into()
    }
}

impl<S: Into<String>> From<S> for Pred {
    fn from(name: S) -> Self {
        Self(name.into())
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

/// Predicate symbol to represent the signature of equality.
pub const EQ_SYM: &str = "=";

#[cfg(test)]
mod tests {
    use crate::{c, f, pred, v};

    #[test]
    fn test_var_to_string() {
        assert_eq!("x", v!(x).to_string());
        assert_eq!("y", v!(y).to_string());
    }

    #[test]
    fn test_func_to_string() {
        assert_eq!("f", f!(f).to_string());
        assert_eq!("g", f!(g).to_string());
    }

    #[test]
    fn test_const_to_string() {
        assert_eq!("'a", c!(a).to_string());
        assert_eq!("'b", c!(b).to_string());
    }

    #[test]
    fn test_pred_to_string() {
        assert_eq!("P", pred!(P).to_string());
        assert_eq!("Q", pred!(Q).to_string());
    }
}
