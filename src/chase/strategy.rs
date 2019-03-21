use crate::chase::{ModelTrait, SelectorTrait, SequentTrait, StrategyTrait};
use std::collections::VecDeque;

/// ### FIFO
/// Arranges the branches of chase computation in a queue to implement a first-in-first-out strategy.
/// > FIFO is used as the basic strategy for benchmarking and testing purposes.
pub struct FIFO<'s, S: 's + SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> {
    queue: VecDeque<(M, Sel)>
}

impl<'s, S: SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> FIFO<'s, S, M, Sel> {
    pub fn new() -> FIFO<'s, S, M, Sel> {
        FIFO { queue: VecDeque::new() }
    }
}

impl<'s, S: SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> StrategyTrait<'s, S, M, Sel> for FIFO<'s, S, M, Sel> {
    fn empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn add(&mut self, model: M, selector: Sel) {
        self.queue.push_back((model, selector))
    }

    fn remove(&mut self) -> Option<(M, Sel)> {
        self.queue.pop_front()
    }
}

/// ### LIFO
/// Arranges the branches of chase computation in a stack to implement a last-in-first-out strategy.
pub struct LIFO<'s, S: 's + SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> {
    queue: VecDeque<(M, Sel)>
}

impl<'s, S: SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> LIFO<'s, S, M, Sel> {
    pub fn new() -> LIFO<'s, S, M, Sel> {
        LIFO { queue: VecDeque::new() }
    }
}

impl<'s, S: SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> StrategyTrait<'s, S, M, Sel> for LIFO<'s, S, M, Sel> {
    fn empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn add(&mut self, model: M, selector: Sel) {
        self.queue.push_front((model, selector))
    }

    fn remove(&mut self) -> Option<(M, Sel)> {
        self.queue.pop_front()
    }
}

#[cfg(test)]
mod test_lifo {
    use super::LIFO;
    use crate::formula::syntax::Theory;
    use crate::chase::{r#impl::basic::{Sequent, Model, Evaluator}, selector::Linear
                       , bounder::DomainSize, StrategyTrait, SelectorTrait, solve_all};
    use std::collections::HashSet;
    use crate::test_prelude::*;
    use std::fs;

    pub fn run_test(theory: &Theory) -> Vec<Model> {
        let geometric_theory = theory.gnf();
        let sequents: Vec<Sequent> = geometric_theory
            .formulas
            .iter()
            .map(|f| f.into()).collect();

        let evaluator = Evaluator {};
        let selector = Linear::new(sequents.iter().collect());
        let mut strategy = LIFO::new();
        let bounder: Option<&DomainSize> = None;
        strategy.add(Model::new(), selector);
        solve_all(&mut strategy, &evaluator, bounder)
    }

    #[test]
    fn test() {
        for item in fs::read_dir("theories/core").unwrap() {
            let theory = read_theory_from_file(item.unwrap().path().display().to_string().as_str());
            let basic_models = solve_basic(&theory);
            let test_models = run_test(&theory);
            let basic_models: HashSet<String> = basic_models.into_iter().map(|m| print_basic_model(m)).collect();
            let test_models: HashSet<String> = test_models.into_iter().map(|m| print_basic_model(m)).collect();
            assert_eq!(basic_models, test_models);
        }
    }
}