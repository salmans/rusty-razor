/*! Implements a number of common transformations on first-order terms and formulae.

A first-order formula reaches geometric sequents ([`GNF`]) by one of two routes: directly from
negation normal form ([`NNF`] → [`GNF`]), removing only the existentials whose scope is not
positive by a [`Geometrization`], or through [`PNF`] → [`SNF`] → [`CNF`] → [`GNF`], Skolemizing
every existential; Razor uses the direct route. [`Relational`] then flattens the conjunctions of
a sequent into atoms over variables. */
mod cnf;
mod dnf;
mod gnf;
mod nnf;
mod pnf;
mod range_restrict;
mod relational;
mod simplify;
mod snf;

pub use cnf::{ToCNF, CNF};
pub use dnf::{ToDNF, DNF};
pub use gnf::{Disjunct, Geometrization, Symbols, ToGNF, GNF, PCF};
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
