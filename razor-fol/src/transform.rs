/*! Implements a number of common transformations on first-order terms and formulae.

A first-order formula becomes a list of geometric sequents in two steps, each a distinct type:
[`NNF`] (negation normal form), then [`GNF`] (standard geometric sequents, Skolemizing only the
existentials whose scope is not positive). [`Relational`] then flattens the conjunctions of a
sequent into atoms over variables. */
mod gnf;
mod nnf;
mod relational;

pub use gnf::{Disjunct, Skolemizer, ToGNF, GNF, PCF};
pub use nnf::{ToNNF, NNF};
pub use relational::{FlatClause, Relational, ToRelational};
