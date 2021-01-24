/*! Defines an abstract syntax tree (AST) for first-order terms and formulae with equality. */
pub mod formula;
mod macros;
pub mod signature;
pub mod symbol;
pub mod term;
mod theory;

pub use formula::{fof::FOF, Formula};
pub use signature::Sig;
pub use symbol::{Const, Func, Pred, Var, EQ_SYM};
pub use term::Term;
pub use theory::Theory;
use thiserror::Error;

/// Is the type of errors arising from inconsistencies in the syntax of formulae.
#[derive(Error, Debug)]
pub enum Error {
    /// Is returned when an unsupported operation is performed on an expression.
    #[error("inconsistent predicate in theory signature `{}` and `{}`", .this.to_string(), .other.to_string())]
    InconsistentPredSig {
        this: signature::PredSig,
        other: signature::PredSig,
    },

    #[error("inconsistent function in theory signature `{}` and `{}`", .this.to_string(), .other.to_string())]
    InconsistentFuncSig {
        this: signature::FuncSig,
        other: signature::FuncSig,
    },
}
