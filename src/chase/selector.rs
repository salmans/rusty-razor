use crate::chase::chase::Selector;
use crate::chase::chase::Sequent;

/// ### Linear
/// Goes through the list of all sequents from the start and returns the next sequent every time
/// `Iterator::next()` is called.
#[derive(Clone)]
pub struct Linear<S: Sequent> {
    sequents: Vec<S>,
}

impl<S: Sequent> Linear<S> {
    pub fn new(sequents: Vec<S>) -> Linear<S> {
        Linear { sequents }
    }
}

impl<S: Sequent> Selector for Linear<S> {}

impl<S: Sequent> Iterator for Linear<S> {
    type Item = S;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if self.sequents.is_empty() {
            None
        } else {
            Some(self.sequents.remove(0))
        }
    }
}

pub struct Fair<S: Sequent> {
    sequents: Vec<S>,
    index: usize,
    start: usize,
    full_circle: bool,
}

impl<S: Sequent> Fair<S> {
    pub fn new(sequents: Vec<S>) -> Fair<S> {
        Fair { sequents, index: 0, start: 0, full_circle: false }
    }
}

impl<S: Sequent> Selector for Fair<S> {}

impl<S: Sequent> Iterator for Fair<S> {
    type Item = S;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if self.sequents.len() == 0 || (self.index == self.start && self.full_circle) {
            return None;
        }
        self.full_circle = true;
        let result = self.sequents.get(self.index).map(|s| s.clone());
        self.index = (self.index + 1) % self.sequents.len();
        result
    }
}

impl<S: Sequent> Clone for Fair<S> {
    fn clone(&self) -> Self {
        Fair {
            sequents: self.sequents.clone(),
            index: self.index,
            start: self.index,
            full_circle: false,
        }
    }
}

#[cfg(test)]
mod test_fair {
    use crate::formula::syntax::Theory;
    use crate::chase::selector::Fair;
    use crate::chase::strategy::FIFO;
    use crate::chase::chase::StrategyNode;
    use crate::chase::chase::solve_all;
    use crate::chase::bounder::DomainSize;
    use crate::chase::chase::Strategy;
    use crate::chase::r#impl::basic::BasicModel;
    use crate::chase::r#impl::basic::BasicSequent;
    use crate::chase::r#impl::basic::BasicEvaluator;
    use crate::test_prelude::solve_basic;
    use crate::test_prelude::read_theory_from_file;
    use crate::test_prelude::CORE_TEST_COUNT;
    use std::collections::HashSet;
    use crate::test_prelude::print_model;

    fn run_test(theory: &Theory) -> Vec<BasicModel> {
        let geometric_theory = theory.gnf();
        let sequents: Vec<BasicSequent> = geometric_theory
            .formulas
            .iter()
            .map(|f| f.into()).collect();

        let evaluator = BasicEvaluator {};
        let selector = Fair::new(sequents);
        let mut strategy = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        strategy.add(StrategyNode::new(BasicModel::new(), selector));
        solve_all(Box::new(strategy), Box::new(evaluator), bounder)
    }

    #[test]
    fn test() {
        for i in 0..=CORE_TEST_COUNT {
            let path = format!("theories/core/thy{}.raz", i);
            let theory = read_theory_from_file(path.as_str());
            let basic_models = solve_basic(&theory);
            let test_models = run_test(&theory);
            let basic_models: HashSet<String> = basic_models.into_iter().map(|m| print_model(m)).collect();
            let test_models: HashSet<String> = test_models.into_iter().map(|m| print_model(m)).collect();
            assert_eq!(basic_models, test_models);
        }
    }
}