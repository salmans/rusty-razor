//! Implements [the chase] based on relational algebra.
//!
//! [the chase]: ../../index.html#the-chase
//!
mod attribute;
mod equation_rewrite;
mod evaluator;
mod expression;
mod memo;
mod model;
mod preprocessor;
mod sequent;

use crate::chase::{r#impl::basic::WitnessTerm, Observation, Rel, WitnessTermTrait, E};
pub use evaluator::Evaluator;
pub use model::Model;
pub use preprocessor::PreProcessor;
use razor_fol::syntax;
pub use sequent::Sequent;
use std::collections::HashMap;
use thiserror::Error;

mod constants {
    use razor_fol::syntax;

    /// The naming prefix of existential attributes and variables in relational formulae.
    pub(super) const EXISTENTIAL_PREFIX: &str = "?";

    /// The naming prefix of equational attributes and variables in relational formulae.
    pub(super) const EQUATIONAL_PREFIX: &str = "~";

    /// The naming prefix of constant predicates created during relationalization
    pub(super) const CONSTANT_PREDICATE_PREFIX: &str = "@";

    /// The naming prefix of functional predicates created during relationalization
    pub(super) const FUNCTIONAL_PREDICATE_PREFIX: &str = "$";

    /// Seperators in different parts of attribute and variable names.
    pub(super) const SEPERATOR: &str = ":";

    /// Is the name of the database instance for domain of elements.
    pub(super) const DOMAIN: &str = "$$domain";

    /// Is the name of the database instance for the equality relation.
    pub(super) const EQUALITY: &str = razor_fol::syntax::EQ_SYM;

    // Create database instance names from symbols:
    #[inline]
    pub(super) fn constant_instance_name(c: &syntax::C) -> String {
        format!("@{}", c.0)
    }

    #[inline]
    pub(super) fn function_instance_name(f: &syntax::F) -> String {
        format!("${}", f.0)
    }

    #[inline]
    pub(super) fn predicate_instance_name(p: &syntax::Pred) -> String {
        p.to_string()
    }
}

/// Is the type of unnamed tuples used in database instances.
type Tuple = Vec<crate::chase::E>;

/// Is a named tuple where every element is identified by an attribute.
type NamedTuple<'a> = HashMap<&'a attribute::Attribute, crate::chase::E>;

/// Returns an empty named tuple.
fn empty_named_tuple<'a>() -> NamedTuple<'a> {
    HashMap::new()
}

/// Is the symbol associated to a relational instance.
#[derive(Hash, PartialEq, Eq, Clone, PartialOrd, Ord, Debug)]
enum Symbol {
    /// Constant symbol
    Const(syntax::C),

    /// Function symbol
    Func { symbol: syntax::F, arity: u8 },

    /// Predicate symbol
    Pred { symbol: syntax::Pred, arity: u8 },

    /// Equality symbol
    Equality,

    /// Domain of elements
    Domain,
}

impl Symbol {
    /// Creates a witness term from symbol, given a list of arguments `E`.
    fn witness(&self, args: &[E]) -> Result<WitnessTerm, Error> {
        match self {
            Symbol::Const(symbol) => {
                assert!(args.len() == 0);

                Ok(WitnessTerm::from(symbol.clone()))
            }
            Symbol::Func { symbol, arity } => {
                assert_eq!(args.len() as u8, *arity);

                let witness = symbol
                    .clone()
                    .app(args.iter().map(|e| e.clone().into()).collect());
                Ok(witness)
            }
            _ => Err(Error::BadWitnessTerm {
                symbol: self.to_string(),
            }),
        }
    }

    /// Creates an observation from the receiver symbol with a slice of `E` as arguments.
    fn observation(&self, args: &[E]) -> Option<Observation<WitnessTerm>> {
        match self {
            Symbol::Pred { symbol, arity } => {
                assert_eq!(args.len() as u8, *arity);

                Some(
                    Rel::from(symbol.clone())
                        .app(args.iter().map(|e| WitnessTerm::from(e.clone())).collect()),
                )
            }
            Symbol::Equality => {
                assert_eq!(args.len(), 2);

                Some(WitnessTerm::from(args[0].clone()).equals(args[1].clone().into()))
            }
            Symbol::Const(c) => {
                assert_eq!(args.len(), 1);

                Some(WitnessTerm::from(c.clone()).equals(WitnessTerm::from(args[0])))
            }
            Symbol::Func { symbol, ref arity } => {
                assert_eq!(args.len() as u8, arity + 1);

                let last = args[*arity as usize];
                let app = symbol.clone().app(
                    args[0..(*arity as usize)]
                        .iter()
                        .map(WitnessTerm::from)
                        .collect(),
                );
                Some(app.equals(last.into()))
            }
            Symbol::Domain => None, // the Domain instance is used only for book-keeping
        }
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display = match self {
            Symbol::Const(c) => format!("constant {}", c.to_string()),
            Symbol::Func { symbol, arity } => {
                format!("function {}, arity {}", symbol.to_string(), arity)
            }
            Symbol::Pred { symbol, arity } => {
                format!("predicate {}, arity {}", symbol.to_string(), arity)
            }
            Symbol::Equality => "equality (=)".into(),
            Symbol::Domain => "domain".into(),
        };
        write!(f, "{}", display)
    }
}

/// Is the type of errors arising from inconsistencies in the syntax of formulae.
#[derive(Error, Debug)]
pub enum Error {
    /// Is returned when an unsupported operation is performed on an expression.
    #[error("bad model initialization: missing symbol `{symbol:?}`")]
    MissingSymbol { symbol: String },

    #[error("database error")]
    DatabaseError {
        #[from]
        source: codd::Error,
    },

    #[error("syntactic transformation error")]
    TransformError {
        #[from]
        source: razor_fol::transform::Error,
    },

    #[error("cannot create witness term for symbol `{symbol:?}`")]
    BadWitnessTerm { symbol: String },

    #[error("expecting flat term, found `{}`", .term.to_string())]
    BadFlatTerm { term: razor_fol::syntax::Term },

    #[error("expecting relational formula, found `{}`", .formula.to_string())]
    BadRelationalFormula { formula: razor_fol::syntax::Formula },

    #[error("cannot build sequent from formula `{}`", .formula.to_string())]
    BadSequentFormula { formula: razor_fol::syntax::Formula },

    #[error("invalid attribute name `{name:?}`")]
    BadAttributeName { name: String },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chase::{
            bounder::DomainSize,
            chase_all,
            scheduler::FIFO,
            strategy::{Bootstrap, Fair},
            PreProcessorEx, SchedulerTrait, StrategyTrait,
        },
        test_prelude::*,
    };
    use razor_fol::syntax::Theory;
    use std::fs;

    fn run(theory: &Theory, pre_processor: &PreProcessor) -> Vec<Model> {
        let (sequents, init_model) = pre_processor.pre_process(theory);

        let evaluator = Evaluator;
        let strategy: Bootstrap<Sequent, Fair<Sequent>> = Bootstrap::new(sequents.iter());
        let mut scheduler = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(init_model, strategy);
        chase_all(&mut scheduler, &evaluator, bounder)
    }

    #[test]
    fn test() {
        for item in fs::read_dir("../theories/core").unwrap() {
            let path = item.unwrap().path().display().to_string();

            let theory = read_theory_from_file(&path);
            let basic_models = solve_basic(&theory);

            let test_models = run(&theory, &PreProcessor::new(true));
            assert_eq!(basic_models.len(), test_models.len());
        }
    }

    #[test]
    fn test_materialized() {
        for item in fs::read_dir("../theories/core").unwrap() {
            let path = item.unwrap().path().display().to_string();
            let theory = read_theory_from_file(&path);

            let simple_models = run(&theory, &PreProcessor::new(false));
            let memoized_models = run(&theory, &PreProcessor::new(true));
            assert_eq!(simple_models.len(), memoized_models.len());
        }
    }
}
