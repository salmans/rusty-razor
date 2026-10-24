/*! Implements a number of common transformations on first-order terms and formulae. */
mod cnf;
mod geometric;
mod gnf;
mod nnf;
mod pnf;
mod relational;
mod snf;

pub use cnf::{ToCNF, CNF};
pub use geometric::{Disjunct, Geometric, ToGeometric};
pub use gnf::{PcfSet, ToGNF, GNF, PCF};
pub use nnf::{ToNNF, NNF};
pub use pnf::{ToPNF, PNF};
pub use relational::{FlatClause, Relational, ToRelational};
pub use snf::{ToSNF, SNF};

use crate::syntax::FOF;
use thiserror::Error;

/// Is the type of errors arising from inconsistencies when transforming formula types.
#[derive(Error, Debug)]
pub enum Error {
    /// Is returned when a [`FOF`] cannot be forced into a [`GNF`].
    #[error("formula `{}` cannot be forced into a GNF", .formula.to_string())]
    FofToGnf { formula: FOF },
}
