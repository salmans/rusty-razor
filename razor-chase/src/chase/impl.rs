//! Contains all implementations of models, sequents and evaluators.
//!
//! The module implements different versions of the Chase and various instances of
//! [`ModelTrait`], [`SequentTrait`] and [`EvaluatorTrait`]
//!
//! [`ModelTrait`]: crate::chase::ModelTrait
//! [`SequentTrait`]: crate::chase::SequentTrait
//! [`EvaluatorTrait`]: crate::chase::EvaluatorTrait
pub mod basic;
pub mod batch;
pub mod reference;
pub mod relational;
