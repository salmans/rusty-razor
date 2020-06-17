/*! Defines an abstract syntax tree (AST) for first-order terms and formulae with equality. */

mod formula;
mod macros;
mod signature;
mod symbol;
mod term;
mod theory;

pub use formula::{exists, forall, not, Formula};
pub use signature::Sig;
pub use symbol::{FApp, Pred, C, F, V};
pub use term::Term;
pub use theory::Theory;
