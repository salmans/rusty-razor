/*! Implements a number of common transformations on first-order terms and formulae. */
mod cnf;
mod dnf;
mod gnf;
mod nnf;
mod pnf;
pub mod relationalize;
mod simplify;
mod snf;
mod substitution;
use thiserror::Error;

pub use cnf::CNF;
pub use dnf::DNF;
pub use gnf::GNF;
pub use nnf::NNF;
pub use pnf::PNF;
pub use snf::SNF;
pub use substitution::{Substitution, TermBased, VariableRenaming};

/// Is the type of errors arising from inconsistencies in the syntax of formulae.
#[derive(Error, Debug)]
pub enum Error {
    /// Is returned when an unsupported operation is performed on an expression.
    #[error("failed to relationalize formula: `{}`", .formula.to_string())]
    RelationalizeFailure { formula: super::syntax::Formula },

    #[error("failed on non-variable term: `{}`", .term.to_string())]
    EqualityExpandNonVar { term: super::syntax::Term },

    #[error("fialed to expand equality for formula: `{}`", .formula.to_string())]
    EqualityExpandUnsupported { formula: super::syntax::Formula },

    #[error("fialed to range restrict formula: `{}`", .formula.to_string())]
    RangeRestrictUnsupported { formula: super::syntax::Formula },
}
