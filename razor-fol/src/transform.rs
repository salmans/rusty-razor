/*! Implements a number of common transformations on first-order terms and formulae. */
mod cnf;
mod dnf;
mod gnf;
mod nnf;
mod pnf;
pub mod relationalize;
mod simplify;
mod snf;
use thiserror::Error;

pub use cnf::{Clause as CNF_Clause, CNF};
pub use dnf::{Clause as DNF_Clause, DNF};
pub use gnf::GNF;
pub use nnf::NNF;
pub use pnf::PNF;
pub use relationalize::Relational;
pub use snf::SNF;

/// Is the type of errors returned by syntactic transformations.
#[derive(Error, Debug)]
pub enum Error {
    /// Is returned when an unsupported operation is performed on an expression.
    #[error("failed to relationalize formula: `{}`", .formula.to_string())]
    RelationalizeFailure { formula: super::syntax::FOF },

    #[error("failed on non-variable term: `{}`", .term.to_string())]
    EqualityExpandNonVar { term: super::syntax::term::Complex },

    #[error("fialed to expand equality for formula: `{}`", .formula.to_string())]
    EqualityExpandUnsupported { formula: super::syntax::FOF },

    #[error("fialed to range restrict formula: `{}`", .formula.to_string())]
    RangeRestrictUnsupported { formula: super::syntax::FOF },
}
