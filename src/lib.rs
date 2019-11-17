/*! Rusty Razor is a tool for constructing finite models for first-order theories with equality.

The model-finding algorithm is inspired by [the Chase](https://en.wikipedia.org/wiki/Chase_(algorithm))
in database systems. Given an input first-order theory, Razor constructs a set of homomorphically
minimal models that satisfy theory.

To learn more about the theoretical foundation of Razor, check out my
[PhD dissertation](https://digitalcommons.wpi.edu/etd-dissertations/458/). */

#![doc(issue_tracker_base_url = "https://github.com/salmans/rusty-razor/issues")]
pub mod formula;
pub mod chase;
pub mod trace;
pub mod utils;

#[cfg(test)]
mod test_prelude;

#[macro_use]
extern crate tracing;