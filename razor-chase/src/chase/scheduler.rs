//! Implements various schedulers for scheduling branches of the Chase.
//!
//! The schedulers are instances of [`SchedulerTrait`].
//!
//! [`SchedulerTrait`]: ../trait.SchedulerTrait.html
use crate::chase::{ModelTrait, SchedulerTrait, SequentTrait, StrategyTrait};
use std::collections::VecDeque;

/// Is a wrapper around other implementations of scheduler, preferred over a trait object that may
/// contain different implementations where a choice among schedulers is desirable.
pub enum Dispatch<'s, S: 's + SequentTrait, M: ModelTrait, Stg: StrategyTrait<Item = &'s S>> {
    /// Wraps a [`FIFO`] scheduler, implementing a first-in-first-out algorithm.
    ///
    /// [`FIFO`]: ./struct.FIFO.html
    FIFO { scheduler: FIFO<'s, S, M, Stg> },

    /// Wraps a [`LIFO`] scheduler, implementing a last-in-first-out algorithm.
    ///
    /// [`LIFO`]: ./struct.LIFO.html
    LIFO { scheduler: LIFO<'s, S, M, Stg> },
}

impl<'s, S, M, Stg> Dispatch<'s, S, M, Stg>
where
    S: 's + SequentTrait,
    M: ModelTrait,
    Stg: StrategyTrait<Item = &'s S>,
{
    /// Returns a [`FIFO`], wrapped in a `Dispatch` scheduler.
    ///
    /// [`FIFO`]: ./struct.FIFO.html
    pub fn new_fifo() -> Self {
        Self::FIFO {
            scheduler: FIFO::new(),
        }
    }

    /// Returns a [`LIFO`], wrapped in a `Dispatch` scheduler.
    ///
    /// [`LIFO`]: ./struct.LIFO.html
    pub fn new_lifo() -> Self {
        Self::LIFO {
            scheduler: LIFO::new(),
        }
    }
}

impl<'s, S, M, Stg> SchedulerTrait<'s, S, M, Stg> for Dispatch<'s, S, M, Stg>
where
    S: 's + SequentTrait,
    M: ModelTrait,
    Stg: StrategyTrait<Item = &'s S>,
{
    fn empty(&self) -> bool {
        match self {
            Self::FIFO { scheduler } => scheduler.empty(),
            Self::LIFO { scheduler } => scheduler.empty(),
        }
    }

    fn add(&mut self, model: M, strategy: Stg) {
        match self {
            Self::FIFO { scheduler } => scheduler.add(model, strategy),
            Self::LIFO { scheduler } => scheduler.add(model, strategy),
        }
    }

    fn remove(&mut self) -> Option<(M, Stg)> {
        match self {
            Dispatch::FIFO { scheduler } => scheduler.remove(),
            Dispatch::LIFO { scheduler } => scheduler.remove(),
        }
    }
}

/// Schedules branches of the Chase in a first-in-first-out manner.
pub struct FIFO<'s, S: 's + SequentTrait, M: ModelTrait, Stg: StrategyTrait<Item = &'s S>> {
    /// Is a queue to store the Chase branches (a [model] together with a [strategy]) in a
    /// first-in-first-out fashion.
    ///
    /// [model]: ../trait.ModelTrait.html
    /// [strategy]: ../trait.StrategyTrait.html
    queue: VecDeque<(M, Stg)>,
}

impl<'s, S, M, Stg> FIFO<'s, S, M, Stg>
where
    S: 's + SequentTrait,
    M: ModelTrait,
    Stg: StrategyTrait<Item = &'s S>,
{
    pub fn new() -> Self {
        FIFO {
            queue: VecDeque::new(),
        }
    }
}

impl<'s, S, M, Stg> SchedulerTrait<'s, S, M, Stg> for FIFO<'s, S, M, Stg>
where
    S: 's + SequentTrait,
    M: ModelTrait,
    Stg: StrategyTrait<Item = &'s S>,
{
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

/// Schedules branches of the Chase in a last-in-first-out manner.
pub struct LIFO<'s, S: 's + SequentTrait, M: ModelTrait, Stg: StrategyTrait<Item = &'s S>> {
    /// Is a queue to store the Chase branches (a [model] together with a [strategy]) in a
    /// last-in-first-out fashion.
    ///
    /// [model]: ../trait.ModelTrait.html
    /// [strategy]: ../trait.StrategyTrait.html
    queue: VecDeque<(M, Stg)>,
}

impl<'s, S, M, Stg> LIFO<'s, S, M, Stg>
where
    S: 's + SequentTrait,
    M: ModelTrait,
    Stg: StrategyTrait<Item = &'s S>,
{
    pub fn new() -> Self {
        LIFO {
            queue: VecDeque::new(),
        }
    }
}

impl<'s, S, M, Stg> SchedulerTrait<'s, S, M, Stg> for LIFO<'s, S, M, Stg>
where
    S: 's + SequentTrait,
    M: ModelTrait,
    Stg: StrategyTrait<Item = &'s S>,
{
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
    use crate::chase::scheduler::LIFO;
    use crate::chase::{
        bounder::DomainSize,
        chase_all,
        r#impl::basic::{Evaluator, Model, Sequent},
        strategy::Linear,
        SchedulerTrait, StrategyTrait,
    };
    use crate::test_prelude::*;
    use razor_fol::syntax::Theory;
    use std::collections::HashSet;
    use std::fs;

    pub fn run_test(theory: &Theory) -> Vec<Model> {
        let geometric_theory = theory.gnf();
        let sequents: Vec<Sequent> = geometric_theory.formulae.iter().map(|f| f.into()).collect();

        let evaluator = Evaluator {};
        let strategy = Linear::new(sequents.iter().collect());
        let mut scheduler = LIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(Model::new(), strategy);
        chase_all(&mut scheduler, &evaluator, bounder)
    }

    #[test]
    fn test() {
        for item in fs::read_dir("../theories/core").unwrap() {
            let theory = read_theory_from_file(item.unwrap().path().display().to_string().as_str());
            let basic_models = solve_basic(&theory);
            let test_models = run_test(&theory);
            let basic_models: HashSet<String> = basic_models
                .into_iter()
                .map(|m| print_basic_model(m))
                .collect();
            let test_models: HashSet<String> = test_models
                .into_iter()
                .map(|m| print_basic_model(m))
                .collect();
            assert_eq!(basic_models, test_models);
        }
    }
}
