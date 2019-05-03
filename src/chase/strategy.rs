use crate::chase::{ModelTrait, SelectorTrait, SequentTrait, StrategyTrait};
use std::collections::VecDeque;

/// A strategy to dispatch work to other strategies.
pub enum Dispatch<'s, S: 's + SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> {
    FIFO { strategy: FIFO<'s, S, M, Sel> },
    LIFO { strategy: LIFO<'s, S, M, Sel> },
}

impl<'s, S, M, Sel> Dispatch<'s, S, M, Sel>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Sel: SelectorTrait<Item=&'s S> {
    pub fn new_fifo() -> Self {
        Dispatch::FIFO { strategy: FIFO::new() }
    }

    pub fn new_lifo() -> Self {
        Dispatch::LIFO { strategy: LIFO::new() }
    }
}

impl<'s, S, M, Sel> StrategyTrait<'s, S, M, Sel> for Dispatch<'s, S, M, Sel>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Sel: SelectorTrait<Item=&'s S> {
    fn empty(&self) -> bool {
        match self {
            Dispatch::FIFO { strategy } => strategy.empty(),
            Dispatch::LIFO { strategy } => strategy.empty(),
        }
    }

    fn add(&mut self, model: M, selector: Sel) {
        match self {
            Dispatch::FIFO { strategy } => strategy.add(model, selector),
            Dispatch::LIFO { strategy } => strategy.add(model, selector),
        }
    }

    fn remove(&mut self) -> Option<(M, Sel)> {
        match self {
            Dispatch::FIFO { strategy } => strategy.remove(),
            Dispatch::LIFO { strategy } => strategy.remove(),
        }
    }
}

/// ### FIFO
/// Arranges the branches of chase computation in a queue to implement a first-in-first-out strategy.
/// > FIFO is used as the basic strategy for benchmarking and testing purposes.
pub struct FIFO<'s, S: 's + SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> {
    queue: VecDeque<(M, Sel)>
}

impl<'s, S, M, Sel> FIFO<'s, S, M, Sel>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Sel: SelectorTrait<Item=&'s S> {
    pub fn new() -> Self {
        FIFO { queue: VecDeque::new() }
    }
}

impl<'s, S, M, Sel> StrategyTrait<'s, S, M, Sel> for FIFO<'s, S, M, Sel>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Sel: SelectorTrait<Item=&'s S> {
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

impl<'s, S, M, Sel> LIFO<'s, S, M, Sel>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Sel: SelectorTrait<Item=&'s S> {
    pub fn new() -> Self {
        LIFO { queue: VecDeque::new() }
    }
}

impl<'s, S, M, Sel> StrategyTrait<'s, S, M, Sel> for LIFO<'s, S, M, Sel>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Sel: SelectorTrait<Item=&'s S> {
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
    use crate::formula::syntax::Theory;
    use crate::chase::{r#impl::basic::{Sequent, Model, Evaluator}, selector::Linear
                       , bounder::DomainSize, StrategyTrait, SelectorTrait, solve_all};
    use std::collections::HashSet;
    use crate::test_prelude::*;
    use std::fs;
    use crate::chase::strategy::LIFO;

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