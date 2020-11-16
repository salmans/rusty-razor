/*! Defines the symbols of ['V'], ['C'], ['F'] and ['Pred'] for making terms and formulae.

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

/// Predicate symbol to represent the signature of equality.
pub const EQ_SYM: &str = "=";

/// Is used to generate symbols in the context of transformations that introduce new `String` symbols.
#[derive(PartialEq, Clone, Debug)]
pub struct Generator {
    /// Is the prefix of generated symbols (default `""`).
    prefix: String,

    /// Is the suffix of generated symbols (default `""`).
    suffix: String,

    /// Is the delimiter between the index symbol and the counter if both are present (default `""`).
    delimiter: String,

    /// Is an internal counter used for generating the next symbol.
    counter: i32,
}

impl Generator {
    /// Creates a new `Generator` with default values.
    pub fn new() -> Self {
        Self {
            prefix: "".into(),
            suffix: "".into(),
            delimiter: "".into(),
            counter: 0,
        }
    }

    /// Creates a new generator that is identical to the receiver except for its `prefix`.
    pub fn set_prefix<S: Into<String>>(&self, prefix: S) -> Self {
        Self {
            prefix: prefix.into(),
            ..self.clone()
        }
    }

    /// Creates a new generator that is identical to the receiver except for its `suffix`.    
    pub fn set_suffix<S: Into<String>>(&self, suffix: S) -> Self {
        Self {
            suffix: suffix.into(),
            ..self.clone()
        }
    }

    /// Creates a new generator that is identical to the receiver except for its `delimiter`.
    pub fn set_delimiter<S: Into<String>>(&self, delimiter: S) -> Self {
        Self {
            delimiter: delimiter.into(),
            ..self.clone()
        }
    }

    /// Generates a new uncounted symbol in between the generator's prefix and suffix.
    pub fn symbol<S: Into<String>>(&self, symbol: S) -> String {
        format!("{}{}{}", self.prefix, symbol.into(), self.suffix)
    }

    /// Generates a new uncounted indexed symbol with generator's prefix, suffix and delimiter.
    pub fn indexed_symbol<S: Into<String>>(&self, symbol: S, index: i32) -> String {
        format!(
            "{}{}{}{}{}",
            self.prefix,
            symbol.into(),
            self.delimiter,
            index,
            self.suffix
        )
    }

    /// Generates a new unindexed counted symbol.
    pub fn generate_next(&mut self) -> String {
        let result = format!("{}{}{}", self.prefix, self.counter, self.suffix);
        self.counter += 1;
        result
    }

    /// Generates a new counted symbol indexed by `symbol`.        
    pub fn generate_next_with_symbol<S: Into<String>>(&mut self, symbol: S) -> String {
        let result = format!(
            "{}{}{}{}{}",
            self.prefix,
            symbol.into(),
            self.delimiter,
            self.counter,
            self.suffix
        );
        self.counter += 1;
        result
    }

    /// Resets the generator by setting its internal counter to 0.
    pub fn reset(&mut self) {
        self.counter = 0;
    }
}

impl Default for Generator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

    #[test]
    fn test_symbol_generator() {
        assert_eq!(
            Generator {
                prefix: "".into(),
                suffix: "".into(),
                delimiter: "".into(),
                counter: 0,
            },
            Generator::new()
        );
        {
            let mut g = Generator::new()
                .set_prefix("$")
                .set_suffix("!")
                .set_delimiter(":");

            assert_eq!("$v!", g.symbol("v"));
            assert_eq!("$0!", g.generate_next());
            assert_eq!("$v:1!", g.generate_next_with_symbol("v"));
            assert_eq!("$v:2!", g.generate_next_with_symbol("v"));
        }
    }
}
