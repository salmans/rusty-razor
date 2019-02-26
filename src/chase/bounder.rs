use crate::chase::chase::Bounder;
use crate::chase::chase::BasicObservation;
use crate::chase::chase::Model;
use crate::chase::chase::E;

pub struct DomainSize {
    max_domain_size: usize,
}

impl DomainSize {
    pub fn new(max_domain_size: usize) -> DomainSize {
        DomainSize { max_domain_size }
    }
}

impl Bounder for DomainSize {
    fn bound<M: Model>(&self, model: &M, observation: &BasicObservation) -> bool {
        match observation {
            BasicObservation::Fact { relation: _, terms } => {
                let model_size = model.domain().len();
                let terms: Vec<Option<E>> = terms.iter()
                    .map(|t| model.element(t))
                    .filter(|t| t.is_none()).collect();
                let size = terms.len();
                model_size + size >= self.max_domain_size
            }
            BasicObservation::Identity { left, right } => {
                let mut size = model.domain().len();
                if model.element(left).is_none() {
                    size += 1;
                }
                if model.element(right).is_none() {
                    size += 1;
                }
                size >= self.max_domain_size
            }
        }
    }
}