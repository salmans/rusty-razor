use super::{Formula, Pred, Term, C, F};
use anyhow::{bail, Error, Result};
use core::convert::TryFrom;
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

#[doc(hidden)]
/// Predicate symbol to represent the signature of equality.
pub const EQ_PRED_SYM: &'static str = "=";

/// contains the signature information for function symbols.
#[derive(PartialEq, Eq, Debug)]
pub struct FSig {
    pub symbol: F,
    pub arity: u8,
}

impl fmt::Display for FSig {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "symbol: {}, arity: {}", self.symbol, self.arity)
    }
}

/// contains the signature information for predicate symbols.
#[derive(PartialEq, Eq, Debug)]
pub struct PSig {
    pub symbol: Pred,
    pub arity: u8,
}

impl fmt::Display for PSig {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "symbol: {}, arity: {}", self.symbol, self.arity)
    }
}

/// is the signature of a first-order theory.
#[derive(PartialEq, Eq, Debug)]
pub struct Sig {
    /// is the constant symbols in a theory.
    pub constants: HashSet<C>,

    /// is the signature of functions in a theory.
    pub functions: HashMap<F, FSig>,

    /// is the signature of predicates in a theory.
    pub predicates: HashMap<Pred, PSig>,
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

    fn add_function(&mut self, function: FSig) -> Result<()> {
        if let Some(sig) = self.functions.get(&function.symbol) {
            if *sig != function {
                bail!(format!(
                    "incompatible function signature \"{}\" and \"{}\" ",
                    sig, function
                ));
            }
        } else {
            self.functions.insert(function.symbol.clone(), function);
        }
        Ok(())
    }

    fn add_predicate(&mut self, predicate: PSig) -> Result<()> {
        if let Some(sig) = self.predicates.get(&predicate.symbol) {
            if *sig != predicate {
                bail!(format!(
                    "incompatible predicate signature \"{}\" and \"{}\" ",
                    sig, predicate
                ));
            }
        } else {
            self.predicates.insert(predicate.symbol.clone(), predicate);
        }
        Ok(())
    }
}

impl TryFrom<&Formula> for Sig {
    type Error = Error;

    fn try_from(value: &Formula) -> Result<Self> {
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

impl TryFrom<&Vec<Formula>> for Sig {
    type Error = Error;

    fn try_from(value: &Vec<Formula>) -> Result<Self, Self::Error> {
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

fn formula_signature(formula: &Formula) -> (Vec<C>, Vec<FSig>, Vec<PSig>) {
    match formula {
        Formula::Top | Formula::Bottom => (Vec::new(), Vec::new(), Vec::new()),
        Formula::Atom { predicate, terms } => {
            let mut constants = Vec::new();
            let mut functions = Vec::new();

            for t in terms {
                let (cs, fs) = term_signature(t);
                constants.extend(cs);
                functions.extend(fs);
            }

            (
                constants,
                functions,
                vec![PSig {
                    symbol: predicate.clone(),
                    arity: terms.len() as u8,
                }],
            )
        }
        Formula::Equals { left, right } => {
            let (cs, fs) = combine_term_signatures(left, right);
            (
                cs,
                fs,
                vec![PSig {
                    symbol: Pred(EQ_PRED_SYM.to_string()),
                    arity: 2,
                }],
            )
        }
        Formula::Not { formula } => formula_signature(formula),
        Formula::And { left, right } => combine_formula_signatures(left, right),
        Formula::Or { left, right } => combine_formula_signatures(left, right),
        Formula::Implies { left, right } => combine_formula_signatures(left, right),
        Formula::Iff { left, right } => combine_formula_signatures(left, right),
        Formula::Exists { formula, .. } => formula_signature(formula),
        Formula::Forall { formula, .. } => formula_signature(formula),
    }
}

fn combine_term_signatures(first: &Term, second: &Term) -> (Vec<C>, Vec<FSig>) {
    let (mut cs, mut fs) = term_signature(first);
    let (rcs, rfs) = term_signature(second);

    cs.extend(rcs);
    fs.extend(rfs);

    (cs, fs)
}

fn combine_formula_signatures(first: &Formula, second: &Formula) -> (Vec<C>, Vec<FSig>, Vec<PSig>) {
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
            let formula = "true".parse::<Formula>().unwrap();
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
            let formula = "P('c)".parse::<Formula>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PSig {
                symbol: Pred(EQ_PRED_SYM.to_string()),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(C("c".to_string()));
            let formula = "'c = 'c".parse::<Formula>().unwrap();
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
            let formula = "P(f(x, 'c))".parse::<Formula>().unwrap();
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
            let formula = "P(f(x, 'c), 'd, f(g(x), y))".parse::<Formula>().unwrap();
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
            let formula = "~P(f('c), y)".parse::<Formula>().unwrap();
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
            let formula = "P(f(x), y) & Q('c)".parse::<Formula>().unwrap();
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
            let formula = "P(f(x), y) | Q('c)".parse::<Formula>().unwrap();
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
            let formula = "P(f(x), y) -> Q('c)".parse::<Formula>().unwrap();
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
            let formula = "P(f(x), y) <=> Q('c)".parse::<Formula>().unwrap();
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
            let formula = "!x. P(f('c), y)".parse::<Formula>().unwrap();
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
            let formula = "?x. P(f('c), y)".parse::<Formula>().unwrap();
            assert_eq!(sig, Sig::try_from(&formula).unwrap());
        }
        {
            let formula = "P(x) & P(x, y)".parse::<Formula>().unwrap();
            assert!(Sig::try_from(&formula).is_err());
        }
        {
            let formula = "P(f(x), f(x, y))".parse::<Formula>().unwrap();
            assert!(Sig::try_from(&formula).is_err());
        }
        {
            let formula = "f(x) = f(x, y)".parse::<Formula>().unwrap();
            assert!(Sig::try_from(&formula).is_err());
        }
        {
            let formula = "P(f(x)) & P(f(x, y))".parse::<Formula>().unwrap();
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
                "P(f('c), y)".parse::<Formula>().unwrap(),
                "Q(g('d), z)".parse::<Formula>().unwrap(),
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
                "P(f('c), y)".parse::<Formula>().unwrap(),
                "P(f('c), y)".parse::<Formula>().unwrap(),
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
                "P(f('c), y)".parse::<Formula>().unwrap(),
                "P(f('c, d), y)".parse::<Formula>().unwrap(),
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
                "P(f('c), y)".parse::<Formula>().unwrap(),
                "P(f('c), y, z)".parse::<Formula>().unwrap(),
            ];
            assert!(Sig::try_from(&formulae).is_err());
        }
    }
}
