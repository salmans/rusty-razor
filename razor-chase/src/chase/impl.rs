//! Contains all implementations of models, sequents and evaluators.
//!
//! The module implements different versions of the chase and various instances of
//! [`Model`], [`Sequent`] and [`Evaluator`]
//!
//! [`Model`]: crate::chase::Model
//! [`Sequent`]: crate::chase::Sequent
//! [`Evaluator`]: crate::chase::Evaluator
pub mod basic;
pub mod batch;
pub mod reference;
pub mod relational;
