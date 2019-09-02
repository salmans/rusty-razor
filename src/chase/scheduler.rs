//! Contains a number of scheduling algorithms.
use crate::chase::{ModelTrait, StrategyTrait, SequentTrait, SchedulerTrait};
use std::collections::VecDeque;

/// A scheduler to dispatch work to other strategies.
pub enum Dispatch<'s, S: 's + SequentTrait, M: ModelTrait, Stg: StrategyTrait<Item=&'s S>> {
    FIFO { scheduler: FIFO<'s, S, M, Stg> },
    LIFO { scheduler: LIFO<'s, S, M, Stg> },
}

impl<'s, S, M, Stg> Dispatch<'s, S, M, Stg>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Stg: StrategyTrait<Item=&'s S> {
    pub fn new_fifo() -> Self {
        Dispatch::FIFO { scheduler: FIFO::new() }
    }

    pub fn new_lifo() -> Self {
        Dispatch::LIFO { scheduler: LIFO::new() }
    }
}

impl<'s, S, M, Stg> SchedulerTrait<'s, S, M, Stg> for Dispatch<'s, S, M, Stg>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Stg: StrategyTrait<Item=&'s S> {
    fn empty(&self) -> bool {
        match self {
            Dispatch::FIFO { scheduler } => scheduler.empty(),
            Dispatch::LIFO { scheduler } => scheduler.empty(),
        }
    }

    fn add(&mut self, model: M, strategy: Stg) {
        match self {
            Dispatch::FIFO { scheduler } => scheduler.add(model, strategy),
            Dispatch::LIFO { scheduler } => scheduler.add(model, strategy),
        }
    }

    fn remove(&mut self) -> Option<(M, Stg)> {
        match self {
            Dispatch::FIFO { scheduler } => scheduler.remove(),
            Dispatch::LIFO { scheduler } => scheduler.remove(),
        }
    }
}

/// ### FIFO
/// Arranges the branches of chase computation in a queue to implement a first-in-first-out scheduler.
/// > FIFO is used as the basic scheduler for benchmarking and testing purposes.
pub struct FIFO<'s, S: 's + SequentTrait, M: ModelTrait, Stg: StrategyTrait<Item=&'s S>> {
    queue: VecDeque<(M, Stg)>
}

impl<'s, S, M, Stg> FIFO<'s, S, M, Stg>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Stg: StrategyTrait<Item=&'s S> {
    pub fn new() -> Self {
        FIFO { queue: VecDeque::new() }
    }
}

impl<'s, S, M, Stg> SchedulerTrait<'s, S, M, Stg> for FIFO<'s, S, M, Stg>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Stg: StrategyTrait<Item=&'s S> {
    fn empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn add(&mut self, model: M, strategy: Stg) {
        self.queue.push_back((model, strategy))
    }

    fn remove(&mut self) -> Option<(M, Stg)> {
        self.queue.pop_front()
    }
}

/// ### LIFO
/// Arranges the branches of chase computation in a stack to implement a last-in-first-out scheduler.
pub struct LIFO<'s, S: 's + SequentTrait, M: ModelTrait, Stg: StrategyTrait<Item=&'s S>> {
    queue: VecDeque<(M, Stg)>
}

impl<'s, S, M, Stg> LIFO<'s, S, M, Stg>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Stg: StrategyTrait<Item=&'s S> {
    pub fn new() -> Self {
        LIFO { queue: VecDeque::new() }
    }
}

impl<'s, S, M, Stg> SchedulerTrait<'s, S, M, Stg> for LIFO<'s, S, M, Stg>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Stg: StrategyTrait<Item=&'s S> {
    fn empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn add(&mut self, model: M, strategy: Stg) {
        self.queue.push_front((model, strategy))
    }

    fn remove(&mut self) -> Option<(M, Stg)> {
        self.queue.pop_front()
    }
}

#[cfg(test)]
mod test_lifo {
    use crate::formula::syntax::Theory;
    use crate::chase::{r#impl::basic::{Sequent, Model, Evaluator}, strategy::Linear
                       , bounder::DomainSize, SchedulerTrait, StrategyTrait, solve_all};
    use std::collections::HashSet;
    use crate::test_prelude::*;
    use std::fs;
    use crate::chase::scheduler::LIFO;

    pub fn run_test(theory: &Theory) -> Vec<Model> {
        let geometric_theory = theory.gnf();
        let sequents: Vec<Sequent> = geometric_theory
            .formulae
            .iter()
            .map(|f| f.into()).collect();

        let evaluator = Evaluator {};
        let strategy = Linear::new(sequents.iter().collect());
        let mut scheduler = LIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(Model::new(), strategy);
        solve_all(&mut scheduler, &evaluator, bounder)
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