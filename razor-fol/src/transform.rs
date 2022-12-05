/*! Implements a number of common transformations on first-order terms and formulae. */
mod cnf;
mod dnf;
mod gnf;
mod linear;
mod nnf;
mod pnf;
mod range_restrict;
mod relational;
mod simplify;
mod snf;

pub use cnf::{Cnf, CnfClauseSet, ToCnf, ToCnfClauseSet};
pub use dnf::{Dnf, DnfClauseSet, ToDnf, ToDnfClauseSet};
pub use gnf::{Gnf, Pcf, PcfSet, ToGnf};
pub use nnf::{Nnf, ToNnf};
pub use pnf::{Pnf, ToPnf};
pub use relational::{FlatClause, Relational, ToRelational};
pub use snf::{Snf, ToSnf};

use crate::syntax::Fof;
use thiserror::Error;

/// Is the type of errors arising from inconsistencies when transforming formula types.
#[derive(Error, Debug)]
pub enum Error {
    /// Is returned when a [`Fof`] cannot be forced into a [`Gnf`].
    #[error("formula `{}` cannot be forced into a GNF", .formula.to_string())]
    FofToGnf { formula: Fof },
}
