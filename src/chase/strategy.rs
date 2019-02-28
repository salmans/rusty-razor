use crate::chase::{Model, Selector, Sequent, Strategy, StrategyNode};
use std::collections::VecDeque;

/// ### FIFO
/// Arranges the branches of chase computation in a queue to implement a first-in-first-out strategy.
/// > FIFO is used as the basic strategy for benchmarking and testing purposes.
pub struct FIFO<S:Sequent, M:Model, Sel: Selector<Item=S>> {
    queue: VecDeque<StrategyNode<S, M, Sel>>
}

impl<S: Sequent, M: Model, Sel: Selector<Item=S>> FIFO<S, M, Sel> {
    pub fn new() -> FIFO<S, M, Sel> {
        FIFO { queue: VecDeque::new() }
    }
}

impl<S: Sequent, M: Model, Sel: Selector<Item=S>> Strategy<S, M, Sel> for FIFO<S, M, Sel> {
    fn empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn add(&mut self, node: StrategyNode<S, M, Sel>) {
        self.queue.push_back(node)
    }

    fn remove(&mut self) -> Option<StrategyNode<S, M, Sel>> {
        self.queue.pop_front()
    }
}

/// ### FIFO
/// Arranges the branches of chase computation in a stack to implement a last-in-first-out strategy.
pub struct LIFO<S:Sequent, M:Model, Sel: Selector<Item=S>> {
    queue: VecDeque<StrategyNode<S, M, Sel>>
}

impl<S: Sequent, M: Model, Sel: Selector<Item=S>> LIFO<S, M, Sel> {
    pub fn new() -> LIFO<S, M, Sel> {
        LIFO { queue: VecDeque::new() }
    }
}

impl<S: Sequent, M: Model, Sel: Selector<Item=S>> Strategy<S, M, Sel> for LIFO<S, M, Sel> {
    fn empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn add(&mut self, node: StrategyNode<S, M, Sel>) {
        self.queue.push_front(node)
    }

    fn remove(&mut self) -> Option<StrategyNode<S, M, Sel>> {
        self.queue.pop_front()
    }
}

#[cfg(test)]
mod test_lifo {
    use crate::formula::syntax::Theory;
    use crate::chase::selector::Linear;
    use crate::chase::bounder::DomainSize;
    use crate::chase::StrategyNode;
    use crate::chase::Strategy;
    use crate::chase::Selector;
    use crate::chase::r#impl::basic::BasicSequent;
    use crate::chase::r#impl::basic::BasicModel;
    use crate::chase::r#impl::basic::BasicEvaluator;
    use crate::chase::solve_all;
    use super::LIFO;
    use std::collections::HashSet;
    use crate::test_prelude::*;
    use std::fs;

    pub fn run_test(theory: &Theory) -> Vec<BasicModel> {
        let geometric_theory = theory.gnf();
        let sequents: Vec<BasicSequent> = geometric_theory
            .formulas
            .iter()
            .map(|f| f.into()).collect();

        let evaluator = BasicEvaluator {};
        let selector = Linear::new(sequents);
        let mut strategy = LIFO::new();
        let bounder: Option<&DomainSize> = None;
        strategy.add(StrategyNode::new(BasicModel::new(), selector));
        solve_all(Box::new(strategy), Box::new(evaluator), bounder)
    }

    #[test]
    fn test() {
        for item in fs::read_dir("theories/core").unwrap() {
            let theory = read_theory_from_file(item.unwrap().path().display().to_string().as_str());
            let basic_models = solve_basic(&theory);
            let test_models = run_test(&theory);
            let basic_models: HashSet<String> = basic_models.into_iter().map(|m| print_model(m)).collect();
            let test_models: HashSet<String> = test_models.into_iter().map(|m| print_model(m)).collect();
            assert_eq!(basic_models, test_models);
        }
    }
}