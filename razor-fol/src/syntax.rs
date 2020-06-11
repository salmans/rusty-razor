/*! Defines an abstract syntax tree (AST) for first-order terms and formulae with equality. */

mod formula;
mod signature;
mod symbol;
mod term;
mod theory;

pub use formula::{
    exists, exists1, exists2, exists3, exists4, exists5, forall, forall1, forall2, forall3,
    forall4, forall5, not, Formula,
};
pub use signature::Sig;
pub use symbol::{FApp, Pred, C, F, V};
pub use term::Term;
pub use theory::Theory;
