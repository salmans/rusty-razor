//! Implements [the chase] based on relational algebra.
//!
//! [the chase]: crate::chase#the-chase
//!
mod attribute;
mod constants;
mod evaluator;
mod expression;
mod model;
mod preprocessor;
mod rewrite;
mod sequent;
mod symbol;

pub use evaluator::Evaluator;
pub use model::Model;
pub use preprocessor::PreProcessor;
pub use sequent::Sequent;
use std::collections::HashMap;
use thiserror::Error;

/// Is the type of unnamed tuples used in database instances.
type Tuple = Vec<crate::chase::E>;

/// Is a named tuple where every element is identified by an attribute.
type NamedTuple<'a> = HashMap<&'a attribute::Attribute, crate::chase::E>;

/// Returns an empty named tuple.
fn empty_named_tuple<'a>() -> NamedTuple<'a> {
    HashMap::new()
}

/// Is the type of errors arising from inconsistencies in the syntax of formulae.
#[derive(Error, Debug)]
pub enum Error {
    /// Is an error returned when an unsupported operation is performed on an expression.
    #[error("missing symbol `{symbol:?}`")]
    MissingSymbol { symbol: String },

    /// Is a wrapper around the underlying database error.
    #[error("database error")]
    DatabaseError {
        #[from]
        source: codd::Error,
    },

    /// Is an error returned when a witness term cannot be constructed.
    #[error("cannot create witness term for symbol `{symbol:?}`")]
    BadWitnessTerm { symbol: String },

    /// Is an error returned when a relational attribute cannot be constructed.
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
    use razor_fol::syntax::{Theory, FOF};
    use std::fs;

    fn run(theory: &Theory<FOF>, pre_processor: &PreProcessor) -> Vec<Model> {
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
