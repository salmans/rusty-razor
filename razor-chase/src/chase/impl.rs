//! Contains all implementations of models, sequents and evaluators.
//!
//! The module implements different versions of the Chase and various instances of
//! [`ModelTrait`], [`SequentTrait`] and [`EvaluatorTrait`]
//!
//! [`ModelTrait`]: ../trait.ModelTrait.html
//! [`SequentTrait`]: ../trait.SequentTrait.html
//! [`EvaluatorTrait`]: ../trait.EvaluatorTrait.html
pub mod basic;
pub mod batch;
pub mod reference;
pub mod relational;
