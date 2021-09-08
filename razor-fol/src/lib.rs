/*! Provides a set of tools for parsing and applying common logical transformations on first-order
formulae in Razor's syntax. */
#[macro_use]
extern crate lalrpop_util;

pub mod parser;
pub mod syntax;
#[cfg(test)]
pub mod test_macros;
pub mod transform;
