/*! Defines an abstract syntax tree (AST) for first-order terms and formulae with equality. */
mod fof;
pub mod formula;
mod macros;
mod signature;
pub mod symbol;
mod term;
mod theory;

pub use fof::FOF;
pub use formula::Formula;
pub use signature::Sig;
pub use symbol::{FApp, Pred, C, EQ_SYM, F, V};
pub use term::Term;
pub use theory::Theory;
use thiserror::Error;

/// Is the type of errors arising from inconsistencies in the syntax of formulae.
#[derive(Error, Debug)]
pub enum Error {
    /// Is returned when an unsupported operation is performed on an expression.
    #[error("inconsistent predicate in theory signature `{}` and `{}`", .this.to_string(), .other.to_string())]
    InconsistentPredSig {
        this: signature::PSig,
        other: signature::PSig,
    },

    #[error("inconsistent function in theory signature `{}` and `{}`", .this.to_string(), .other.to_string())]
    InconsistentFuncSig {
        this: signature::FSig,
        other: signature::FSig,
    },
}
