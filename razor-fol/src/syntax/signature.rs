/*! Defines a ['Sig'] to represent the signature of first-order theories.

['Sig']: crate::syntax::Sig
*/
use super::{Error, Pred, Term, C, EQ_SYM, F, FOF};
use core::convert::TryFrom;
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
    fn new() -> Self {
        Self {
            constants: HashSet::new(),
            functions: HashMap::new(),
            predicates: HashMap::new(),
        }
    }

    // inserts a new constant in the signature.
    fn add_constant(&mut self, constant: C) {
        self.constants.insert(constant);
    }

    // adds the signature of a function.
    fn add_function(&mut self, function: FSig) -> Result<(), Error> {
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

    // adds the signature of a predicate.
    fn add_predicate(&mut self, predicate: PSig) -> Result<(), Error> {
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

    /// Returns the constants of this signature.
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

impl TryFrom<&FOF> for Sig {
    type Error = Error;

    fn try_from(value: &FOF) -> Result<Self, Error> {
        let mut sig = Sig::new();
        let (cs, fs, ps) = formula_signature(&value);

        for c in cs {
            sig.add_constant(c);
        }

        for f in fs {
            sig.add_function(f)?;
        }

        for p in ps {
            sig.add_predicate(p)?;
        }

        Ok(sig)
    }
}

impl TryFrom<&Vec<FOF>> for Sig {
    type Error = Error;

    fn try_from(value: &Vec<FOF>) -> Result<Self, Self::Error> {
        let mut sig = Sig::new();

        for f in value {
            let (cs, fs, ps) = formula_signature(f);

            for c in cs {
                sig.add_constant(c);
            }

            for f in fs {
                sig.add_function(f)?;
            }

            for p in ps {
                sig.add_predicate(p)?;
            }
        }

        Ok(sig)
    }
}

// returns the constants and function signatures in the input term and its
// subterms and fails if a functions with different signatures exist.
fn term_signature(term: &Term) -> (Vec<C>, Vec<FSig>) {
    match term {
        Term::Var { .. } => (Vec::new(), Vec::new()),
        Term::Const { constant } => (vec![constant.clone()], Vec::new()),
        Term::App { function, terms } => {
            let mut constants = Vec::new();
            let mut functions = Vec::new();

            for t in terms {
                let (cs, fs) = term_signature(t);
                constants.extend(cs);
                functions.extend(fs);
            }

            functions.push(FSig {
                symbol: function.clone(),
                arity: terms.len() as u8,
            });

            (constants, functions)
        }
    }
}

// returns the constants, functions signatures and predicates signatures in
// the given first-order formula and its subformulae and fails if a function or a predicate
// with different signatures exist.
fn formula_signature(formula: &FOF) -> (Vec<C>, Vec<FSig>, Vec<PSig>) {
    match formula {
        FOF::Top | FOF::Bottom => (Vec::new(), Vec::new(), Vec::new()),
        FOF::Atom(this) => {
            let terms = &this.terms;

            let mut constants = Vec::new();
            let mut functions = Vec::new();

            for t in terms {
                let (cs, fs) = term_signature(&t);
                constants.extend(cs);
                functions.extend(fs);
            }

            (
                constants,
                functions,
                vec![PSig {
                    symbol: this.predicate.clone(),
                    arity: terms.len() as u8,
                }],
            )
        }
        FOF::Equals(this) => {
            let (cs, fs) = combine_term_signatures(&this.left, &this.right);
            (
                cs,
                fs,
                vec![PSig {
                    symbol: Pred(EQ_SYM.to_string()),
                    arity: 2,
                }],
            )
        }
        FOF::Not(this) => formula_signature(&this.formula),
        FOF::And(this) => combine_formula_signatures(&this.left, &this.right),
        FOF::Or(this) => combine_formula_signatures(&this.left, &this.right),
        FOF::Implies(this) => combine_formula_signatures(&this.premise, &this.consequence),
        FOF::Iff(this) => combine_formula_signatures(&this.left, &this.right),
        FOF::Exists(this) => formula_signature(&this.formula),
        FOF::Forall(this) => formula_signature(&this.formula),
    }
}

fn combine_term_signatures(first: &Term, second: &Term) -> (Vec<C>, Vec<FSig>) {
    let (mut cs, mut fs) = term_signature(first);
    let (rcs, rfs) = term_signature(second);

    cs.extend(rcs);
    fs.extend(rfs);

    (cs, fs)
}

fn combine_formula_signatures(first: &FOF, second: &FOF) -> (Vec<C>, Vec<FSig>, Vec<PSig>) {
    let (mut cs, mut fs, mut ps) = formula_signature(first);
    let (rcs, rfs, rps) = formula_signature(second);

    cs.extend(rcs);
    fs.extend(rfs);
    ps.extend(rps);

    (cs, fs, ps)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sig_from_formula() {
        {
            let sig = Sig::new();
            let formula = "true".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "P('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred(EQ_SYM.to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "'c = 'c".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "P(f(x, 'c))".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 3,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("g".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            sig.add_constant(C("d".to_string()));
            let formula = "P(f(x, 'c), 'd, f(g(x), y))".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "~P(f('c), y)".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred("Q".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "P(f(x), y) & Q('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred("Q".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "P(f(x), y) | Q('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred("Q".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "P(f(x), y) -> Q('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred("Q".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "P(f(x), y) <=> Q('c)".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "!x. P(f('c), y)".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "?x. P(f('c), y)".parse::<FOF>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let formula = "P(x) & P(x, y)".parse::<FOF>().unwrap();
            assert!(Sig::try_from(&formula).is_err());
        }
        {
            let formula = "P(f(x), f(x, y))".parse::<FOF>().unwrap();
            assert!(Sig::try_from(&formula).is_err());
        }
        {
            let formula = "f(x) = f(x, y)".parse::<FOF>().unwrap();
            assert!(Sig::try_from(&formula).is_err());
        }
        {
            let formula = "P(f(x)) & P(f(x, y))".parse::<FOF>().unwrap();
            assert!(Sig::try_from(&formula).is_err());
        }
    }

    #[test]
    fn test_sig_from_formulae() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred("Q".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("g".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            sig.add_constant(C("d".to_string()));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "Q(g('d), z)".parse::<FOF>().unwrap(),
            ];
            assert_eq!(sig, Sig::try_from(&formulae).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c), y)".parse::<FOF>().unwrap(),
            ];
            assert_eq!(sig, Sig::try_from(&formulae).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c, d), y)".parse::<FOF>().unwrap(),
            ];
            assert!(Sig::try_from(&formulae).is_err());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred("P".to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: F("f".to_string()),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formulae = vec![
                "P(f('c), y)".parse::<FOF>().unwrap(),
                "P(f('c), y, z)".parse::<FOF>().unwrap(),
            ];
            assert!(Sig::try_from(&formulae).is_err());
        }
    }
}
