/*! Defines a ['Sig'] to represent the signature of first-order theories.

['Sig']: crate::syntax::Sig
*/
use super::{Error, Pred, C, F};
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

/// Contains the signature information for a function.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FSig {
    /// Is the function symbol.
    pub symbol: F,

    /// Is the arity of the function.
    pub arity: u8,
}

impl fmt::Display for FSig {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "predicate: {}, arity: {}", self.symbol, self.arity)
    }
}

/// Contains the signature information for a predicate.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PSig {
    /// Is the predicate symbol.
    pub symbol: Pred,

    /// Is the arity of the predicate.
    pub arity: u8,
}

impl fmt::Display for PSig {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "function: {}, arity: {}", self.symbol, self.arity)
    }
}

/// Is the signature of a first-order theory.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Sig {
    /// Is the constant symbols in a theory.
    constants: HashSet<C>,

    /// Is the signature of functions in a theory.
    functions: HashMap<F, FSig>,

    /// Is the signature of predicates in a theory.
    predicates: HashMap<Pred, PSig>,
}

impl Sig {
    /// Creates an empty signature.
    pub(crate) fn new() -> Self {
        Self {
            constants: HashSet::new(),
            functions: HashMap::new(),
            predicates: HashMap::new(),
        }
    }

    /// Creates a new signature by merging the items of an iterator over signatures.
    pub(crate) fn new_from_signatures<I>(value: I) -> Result<Self, Error>
    where
        I: IntoIterator<Item = Sig>,
    {
        let mut sig = Self::new();
        for s in value {
            sig = sig.merge(s)?;
        }
        Ok(sig)
    }

    /// Inserts a new constant in the receiver signature.
    pub(crate) fn add_constant(&mut self, constant: C) {
        self.constants.insert(constant);
    }

    /// Adds the signature of a function to the reciever.
    pub(crate) fn add_function(&mut self, function: FSig) -> Result<(), Error> {
        if let Some(sig) = self.functions.get(&function.symbol) {
            if *sig != function {
                return Err(Error::InconsistentFuncSig {
                    this: sig.clone(),
                    other: function,
                });
            }
        } else {
            self.functions.insert(function.symbol.clone(), function);
        }
        Ok(())
    }

    /// Adds the signature of a predicate to the reciever.
    pub(crate) fn add_predicate(&mut self, predicate: PSig) -> Result<(), Error> {
        if let Some(sig) = self.predicates.get(&predicate.symbol) {
            if *sig != predicate {
                return Err(Error::InconsistentPredSig {
                    this: sig.clone(),
                    other: predicate,
                });
            }
        } else {
            self.predicates.insert(predicate.symbol.clone(), predicate);
        }
        Ok(())
    }

    /// Returns a signature that combines the receiver signature with the signature of `other`.
    pub(crate) fn merge(mut self, other: Self) -> Result<Self, Error> {
        for c in other.constants {
            self.add_constant(c);
        }
        for f in other.functions.values() {
            self.add_function(f.clone())?;
        }
        for p in other.predicates.values() {
            self.add_predicate(p.clone())?;
        }

        Ok(self)
    }

    /// returns the constants of this signature.
    pub fn constants(&self) -> &HashSet<C> {
        &self.constants
    }

    /// Returns the function of this signature.
    pub fn functions(&self) -> &HashMap<F, FSig> {
        &self.functions
    }

    /// Returns the predicates of this signature.
    pub fn predicates(&self) -> &HashMap<Pred, PSig> {
        &self.predicates
    }
}

impl Default for Sig {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{Formula, EQ_SYM, FOF};

    #[test]
    fn test_sig_from_formula() {
        {
            let sig = Sig::new();
            let formula = "true".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "P('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from(EQ_SYM),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "'c = 'c".parse::<FOF>().unwrap();
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
                symbol: F::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "P(f(x, 'c))".parse::<FOF>().unwrap();
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
                symbol: F::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("g"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            sig.add_constant(C::from("d"));
            let formula = "P(f(x, 'c), 'd, f(g(x), y))".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "~P(f('c), y)".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
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
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "P(f(x), y) & Q('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
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
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "P(f(x), y) | Q('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
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
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "P(f(x), y) -> Q('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
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
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "P(f(x), y) <=> Q('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "!x. P(f('c), y)".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formula = "?x. P(f('c), y)".parse::<FOF>().unwrap();
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = "P(x) & P(x, y)".parse::<FOF>().unwrap();
            assert!(formula.signature().is_err());
        }
        {
            let formula = "P(f(x), f(x, y))".parse::<FOF>().unwrap();
            assert!(formula.signature().is_err());
        }
        {
            let formula = "f(x) = f(x, y)".parse::<FOF>().unwrap();
            assert!(formula.signature().is_err());
        }
        {
            let formula = "P(f(x)) & P(f(x, y))".parse::<FOF>().unwrap();
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn test_sig_from_formulae() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("g"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            sig.add_constant(C::from("d"));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "Q(g('d), z)".parse::<FOF>().unwrap(),
            ];
            assert_eq!(
                sig,
                Sig::new_from_signatures(
                    formulae
                        .iter()
                        .map(|f| f.signature())
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap()
                )
                .unwrap()
            );
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c), y)".parse::<FOF>().unwrap(),
            ];
            assert_eq!(
                sig,
                Sig::new_from_signatures(
                    formulae
                        .iter()
                        .map(|f| f.signature())
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap()
                )
                .unwrap()
            );
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c, d), y)".parse::<FOF>().unwrap(),
            ];
            assert!(Sig::new_from_signatures(
                formulae
                    .iter()
                    .map(|f| f.signature())
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap()
            )
            .is_err());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C::from("c"));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c), y, z)".parse::<FOF>().unwrap(),
            ];
            assert!(Sig::new_from_signatures(
                formulae
                    .iter()
                    .map(|f| f.signature())
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap()
            )
            .is_err());
        }
    }
}
