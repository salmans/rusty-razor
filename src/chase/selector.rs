use crate::chase::chase::Selector;
use crate::chase::chase::Sequent;

#[derive(Clone)]
pub struct TopDown<S: Sequent> {
    sequents: Vec<S>,
}

impl<S: Sequent> TopDown<S> {
    pub fn new(sequents: Vec<S>) -> TopDown<S> {
        TopDown { sequents }
    }
}

impl<S: Sequent> Selector for TopDown<S> {}

impl<S: Sequent> Iterator for TopDown<S> {
    type Item = S;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if self.sequents.is_empty() {
            None
        } else {
            Some(self.sequents.remove(0))
        }
    }
}