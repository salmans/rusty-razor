//! Implements various implementations for [`BounderTrait`].
//!
//! [`BounderTrait`]: ../trait.BounderTrait.html
use crate::chase::{BounderTrait, ModelTrait, WitnessTermTrait, Observation};

/// Bounds the size of a [model] by the number of elements in its [domain].
///
/// [model]: ../trait.ModelTrait.html
/// [domain]: ../trait.ModelTrait.html#tymethod.domain
pub struct DomainSize {
    /// Is the maximum size of the [domain] of elements for models accepted by this bounder.
    ///
    /// [domain]: ../trait.ModelTrait.html#tymethod.domain
    max_domain_size: usize,
}

impl From<usize> for DomainSize {
    fn from(size : usize) -> Self {
        Self { max_domain_size: size }
    }
}

impl BounderTrait for DomainSize {
    fn bound<M: ModelTrait>(&self, model: &M, observation: &Observation<M::TermType>) -> bool {
        match observation {
            Observation::Fact { relation: _, terms } => {
                let model_size = model.domain().len();
                let terms: Vec<Option<&<<M as ModelTrait>::TermType as WitnessTermTrait>::ElementType>> = terms.iter()
                    .map(|t| model.element(t))
                    .filter(|t| t.is_none()).collect();
                let size = terms.len();
                model_size + size > self.max_domain_size
            }
            Observation::Identity { left, right } => {
                let mut size = model.domain().len();
                if model.element(left).is_none() {
                    size += 1;
                }
                if model.element(right).is_none() {
                    size += 1;
                }
                size > self.max_domain_size
            }
        }
    }
}