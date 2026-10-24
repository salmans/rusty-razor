/*! Provides a set of tools for parsing and applying common logical transformations on first-order
formulae in Razor's syntax.

A parsed [`FOF`] is converted to negation normal form ([`NNF`]) and from there straight to
standard geometric sequents ([`GNF`]), which Skolemize only the existentials whose scope is not
positive; [`Relational`] flattens their conjunctions for the chase.

[`FOF`]: crate::syntax::FOF
[`NNF`]: crate::transform::NNF
[`GNF`]: crate::transform::GNF
[`Relational`]: crate::transform::Relational
*/
#[macro_use]
extern crate lalrpop_util;

pub mod parser;
pub mod syntax;
pub mod transform;

#[cfg(test)]
pub mod test_macros;
