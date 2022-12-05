//! Provides an implementation of the chase based on relational algebra.
mod attribute;
mod constants;
mod evaluator;
mod expression;
mod model;
mod pre_processor;
mod rewrite;
mod sequent;
mod symbol;

pub use evaluator::RelEvaluator;
pub use model::RelModel;
pub use pre_processor::RelPreProcessor;
pub use sequent::RelSequent;

use razor_fol::syntax::{formula::Atom, term::Variable};
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
    /// Is returned when an unsupported operation is performed on an expression.
    #[error("missing symbol `{symbol:?}`")]
    MissingSymbol { symbol: String },

    /// Is a wrapper around the underlying database error.
    #[error("database error")]
    DatabaseError {
        #[from]
        source: codd::Error,
    },

    /// Is returned when a witness term cannot be constructed.
    #[error("cannot create witness term for symbol `{symbol:?}`")]
    BadWitnessTerm { symbol: String },

    /// Is returned when a relational attribute cannot be constructed.
    #[error("invalid attribute name `{name:?}`")]
    BadAttributeName { name: String },

    /// Is returned when a relationalized atom is of a wrong arity.
    #[error("invalid relational function application `{atom:?}`")]
    BadRelationalAtom { atom: Atom<Variable> },

    /// Is returned when an existential variable is not the output
    /// of one of the previous functional literals in the head of a sequent.
    #[error("existential variable with no origin `{var:?}`")]
    BadExistentialVariable { var: Variable },
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
            PreProcessor, Scheduler,
        },
        test_prelude::*,
    };
    use razor_fol::syntax::{Fof, Theory};

    fn run(theory: &Theory<Fof>, pre_processor: &RelPreProcessor) -> Vec<RelModel> {
        let (sequents, init_model) = pre_processor.pre_process(theory);

        let evaluator = RelEvaluator;
        let strategy: Bootstrap<_, Fair<_>> = sequents.iter().collect();
        let mut scheduler = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(init_model, strategy);
        chase_all(&mut scheduler, &evaluator, bounder)
    }

    #[test]
    fn test() {
        std::fs::read_dir("../theories/core")
            .unwrap()
            .map(|item| item.unwrap().path())
            .filter(|path| path.ends_with(".raz"))
            .for_each(|path| {
                let theory = read_theory_from_file(path.to_str().unwrap());
                let expected_len = read_file(path.with_extension("model").to_str().unwrap())
                    .split("\n-- -- -- -- -- -- -- -- -- --\n")
                    .filter(|s| !s.is_empty())
                    .map(|_| ())
                    .collect::<Vec<_>>()
                    .len();
                let result_len = run(&theory, &RelPreProcessor::new(false)).len();
                assert_eq!(
                    expected_len,
                    result_len,
                    "invalid result for theory {}",
                    path.with_extension("").to_str().unwrap()
                );
            });
    }

    #[test]
    fn test_materialized() {
        std::fs::read_dir("../theories/core")
            .unwrap()
            .map(|item| item.unwrap().path())
            .filter(|path| path.ends_with(".raz"))
            .for_each(|path| {
                let theory = read_theory_from_file(path.to_str().unwrap());
                let expected = run(&theory, &RelPreProcessor::new(false))
                    .into_iter()
                    .map(|m| format!("{:?}", m))
                    .collect::<Vec<_>>();
                let result = run(&theory, &RelPreProcessor::new(true))
                    .into_iter()
                    .map(|m| format!("{:?}", m))
                    .collect::<Vec<_>>();
                assert_eq!(
                    expected,
                    result,
                    "invalid result for theory {}",
                    path.with_extension("").to_str().unwrap()
                );
            });
    }
}
