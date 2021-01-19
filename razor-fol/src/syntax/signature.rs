/*! Defines a ['Sig'] to represent the signature of first-order theories.

['Sig']: crate::syntax::Sig
*/
use super::{Const, Error, Func, Pred};
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

/// Contains the signature information for a [`Func`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FuncSig {
    /// Is the function symbol.
    pub symbol: Func,

    /// Is the arity of the function.
    pub arity: u8,
}

impl fmt::Display for FuncSig {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "predicate: {}, arity: {}", self.symbol, self.arity)
    }
}

/// Contains the signature information for a [`Pred`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PredSig {
    /// Is the predicate symbol.
    pub symbol: Pred,

    /// Is the arity of the predicate.
    pub arity: u8,
}

impl fmt::Display for PredSig {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "function: {}, arity: {}", self.symbol, self.arity)
    }
}

/// Is the signature of a first-order theory.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Sig {
    /// Is the constant symbols in the signature.
    constants: HashSet<Const>,

    /// Is the signature of functions.
    functions: HashMap<String, FuncSig>,

    /// Is the signature of predicates.
    predicates: HashMap<String, PredSig>,
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
    pub(crate) fn from_signatures<I>(value: I) -> Result<Self, Error>
    where
        I: IntoIterator<Item = Sig>,
    {
        let mut sig = Self::new();
        for s in value {
            sig = sig.merge(s)?;
        }
        Ok(sig)
    }

    /// Inserts a new [`Const`] in the receiver signature.
    pub(crate) fn add_constant(&mut self, constant: Const) {
        self.constants.insert(constant);
    }

    /// Inserts the signature [`FuncSig`] of a function [`Func`] to the reciever.
    pub(crate) fn add_function(&mut self, function: FuncSig) -> Result<(), Error> {
        if let Some(sig) = self.functions.get(function.symbol.name()) {
            if *sig != function {
                return Err(Error::InconsistentFuncSig {
                    this: sig.clone(),
                    other: function,
                });
            }
        } else {
            self.functions
                .insert(function.symbol.name().into(), function);
        }
        Ok(())
    }

    /// Inserts the signature [`PredSig`] of a predicate [`Pred`] to the reciever.
    pub(crate) fn add_predicate(&mut self, predicate: PredSig) -> Result<(), Error> {
        if let Some(sig) = self.predicates.get(predicate.symbol.name()) {
            if *sig != predicate {
                return Err(Error::InconsistentPredSig {
                    this: sig.clone(),
                    other: predicate,
                });
            }
        } else {
            self.predicates
                .insert(predicate.symbol.name().into(), predicate);
        }
        Ok(())
    }

    /// Returns a signature that combines the receiver with of `other`.
    pub(crate) fn merge(self, other: Self) -> Result<Self, Error> {
        let mut sig = self;

        for c in other.constants {
            sig.add_constant(c);
        }
        for f in other.functions.values() {
            sig.add_function(f.clone())?;
        }
        for p in other.predicates.values() {
            sig.add_predicate(p.clone())?;
        }

        Ok(sig)
    }

    /// Returns the set [`Const`]s in this signature.
    pub fn constants(&self) -> &HashSet<Const> {
        &self.constants
    }

    /// Returns the function signatures in the receiver in the form of a map from
    /// function names to [`FuncSig`].
    pub fn functions(&self) -> &HashMap<String, FuncSig> {
        &self.functions
    }

    /// Returns the predicate signatures in the receiver in the form of a map from
    /// predicate names to [`PredSig`].    
    pub fn predicates(&self) -> &HashMap<String, PredSig> {
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
    use crate::syntax::{Formula, FOF};

    #[test]
    fn test_merge() {
        {
            let sig = Sig::default();
            let other = Sig::default();
            assert_eq!(Sig::default(), sig.merge(other).unwrap());
        }
        {
            let mut sig = Sig::default();
            sig.add_predicate(PredSig {
                symbol: "P".into(),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: "f".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_constant("c".into());
            let other = Sig::default();

            let expected = sig.clone();
            assert_eq!(expected, sig.merge(other).unwrap());
        }
        {
            let mut sig = Sig::default();
            sig.add_predicate(PredSig {
                symbol: "P".into(),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: "f".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_constant("c".into());

            let mut other = Sig::default();
            other
                .add_predicate(PredSig {
                    symbol: "Q".into(),
                    arity: 2,
                })
                .unwrap();
            other
                .add_function(FuncSig {
                    symbol: "g".into(),
                    arity: 3,
                })
                .unwrap();
            other.add_constant("d".into());

            let mut expected = Sig::default();
            expected
                .add_predicate(PredSig {
                    symbol: "P".into(),
                    arity: 1,
                })
                .unwrap();
            expected
                .add_function(FuncSig {
                    symbol: "f".into(),
                    arity: 2,
                })
                .unwrap();
            expected.add_constant("c".into());
            expected
                .add_predicate(PredSig {
                    symbol: "Q".into(),
                    arity: 2,
                })
                .unwrap();
            expected
                .add_function(FuncSig {
                    symbol: "g".into(),
                    arity: 3,
                })
                .unwrap();
            expected.add_constant("d".into());

            assert_eq!(expected, sig.merge(other).unwrap());
        }
        {
            let mut sig = Sig::default();
            sig.add_predicate(PredSig {
                symbol: "P".into(),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: "f".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_constant("c".into());

            let other = sig.clone();
            let expected = sig.clone();

            assert_eq!(expected, sig.merge(other).unwrap());
        }
        {
            let mut sig = Sig::default();
            sig.add_predicate(PredSig {
                symbol: "P".into(),
                arity: 1,
            })
            .unwrap();

            let mut other = Sig::default();
            other
                .add_predicate(PredSig {
                    symbol: "P".into(),
                    arity: 2,
                })
                .unwrap();

            assert!(sig.merge(other).is_err());
        }
        {
            let mut sig = Sig::default();
            sig.add_function(FuncSig {
                symbol: "f".into(),
                arity: 1,
            })
            .unwrap();

            let mut other = Sig::default();
            other
                .add_function(FuncSig {
                    symbol: "f".into(),
                    arity: 2,
                })
                .unwrap();

            assert!(sig.merge(other).is_err());
        }
        {
            let mut sig = Sig::default();
            sig.add_constant("c".into());

            let mut other = Sig::default();
            other.add_constant("c".into());

            assert!(sig.merge(other).is_ok());
        }
    }

    #[test]
    fn test_from_signatures() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: Pred::from("Q"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("g"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            sig.add_constant(Const::from("d"));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "Q(g('d), z)".parse::<FOF>().unwrap(),
            ];
            assert_eq!(
                sig,
                Sig::from_signatures(
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
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c), y)".parse::<FOF>().unwrap(),
            ];
            assert_eq!(
                sig,
                Sig::from_signatures(
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
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c, d), y)".parse::<FOF>().unwrap(),
            ];
            assert!(Sig::from_signatures(
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
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c), y, z)".parse::<FOF>().unwrap(),
            ];
            assert!(Sig::from_signatures(
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
