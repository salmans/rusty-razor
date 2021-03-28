//! Implements various schedulers for scheduling branches of the chase.
//!
//! The schedulers are instances of [`Scheduler`].
//!
//! [`Scheduler`]: crate::chase::Scheduler
use crate::chase::{Model, Scheduler, Sequent, Strategy};
use std::collections::VecDeque;
use std::marker::PhantomData;

/// Is a wrapper around other implementations of scheduler, preferred over a trait object that may
/// contain different implementations where a choice among schedulers is desirable.
pub enum Dispatch<S: Sequent, M: Model, Stg: Strategy<S>> {
    /// Wraps a [`FIFO`] scheduler, implementing a first-in-first-out algorithm.
    FIFO { scheduler: FIFO<S, M, Stg> },

    /// Wraps a [`LIFO`] scheduler, implementing a last-in-first-out algorithm.
    LIFO {
        scheduler: LIFO<S, M, Stg>,
        _marker: PhantomData<S>,
    },
}

impl<S, M, Stg> Dispatch<S, M, Stg>
where
    S: Sequent,
    M: Model,
    Stg: Strategy<S>,
{
    /// Returns a [`FIFO`], wrapped in a `Dispatch` scheduler.
    pub fn new_fifo() -> Self {
        Self::FIFO {
            scheduler: FIFO::new(),
        }
    }

    /// Returns a [`LIFO`], wrapped in a `Dispatch` scheduler.
    pub fn new_lifo() -> Self {
        Self::LIFO {
            scheduler: LIFO::new(),
            _marker: PhantomData,
        }
    }
}

impl<S, M, Stg> Scheduler<S, M, Stg> for Dispatch<S, M, Stg>
where
    S: Sequent,
    M: Model,
    Stg: Strategy<S>,
{
    fn empty(&self) -> bool {
        match self {
            Self::FIFO { scheduler } => scheduler.empty(),
            Self::LIFO {
                scheduler,
                _marker: PhantomData,
            } => scheduler.empty(),
        }
    }

    fn add(&mut self, model: M, strategy: Stg) {
        match self {
            Self::FIFO { scheduler } => scheduler.add(model, strategy),
            Self::LIFO {
                scheduler,
                _marker: PhantomData,
            } => scheduler.add(model, strategy),
        }
    }

    fn remove(&mut self) -> Option<(M, Stg)> {
        match self {
            Dispatch::FIFO { scheduler } => scheduler.remove(),
            Dispatch::LIFO {
                scheduler,
                _marker: PhantomData,
            } => scheduler.remove(),
        }
    }
}

/// Schedules branches of the chase in a first-in-first-out manner.
pub struct FIFO<S: Sequent, M: Model, Stg: Strategy<S>> {
    /// Is a queue to store the chase branches (a [model] together with a [strategy]) in a
    /// first-in-first-out fashion.
    ///
    /// [model]: crate::chase::Model
    /// [strategy]: crate::chase::Strategy
    queue: VecDeque<(M, Stg)>,
    _marker: PhantomData<S>,
}

impl<S, M, Stg> FIFO<S, M, Stg>
where
    S: Sequent,
    M: Model,
    Stg: Strategy<S>,
{
    pub fn new() -> Self {
        FIFO {
            queue: VecDeque::new(),
            _marker: PhantomData,
        }
    }
}

impl<S, M, Stg> Default for FIFO<S, M, Stg>
where
    S: Sequent,
    M: Model,
    Stg: Strategy<S>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<S, M, Stg> Scheduler<S, M, Stg> for FIFO<S, M, Stg>
where
    S: Sequent,
    M: Model,
    Stg: Strategy<S>,
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

/// Schedules branches of the chase in a last-in-first-out manner.
pub struct LIFO<S: Sequent, M: Model, Stg: Strategy<S>> {
    /// Is a queue to store the chase branches (a [model] together with a [strategy]) in a
    /// last-in-first-out fashion.
    ///
    /// [model]: crate::chase::Model
    /// [strategy]: crate::chase::Strategy
    queue: VecDeque<(M, Stg)>,
    _marker: PhantomData<S>,
}

impl<S, M, Stg> LIFO<S, M, Stg>
where
    S: Sequent,
    M: Model,
    Stg: Strategy<S>,
{
    pub fn new() -> Self {
        LIFO {
            queue: VecDeque::new(),
            _marker: PhantomData,
        }
    }
}

impl<S, M, Stg> Default for LIFO<S, M, Stg>
where
    S: Sequent,
    M: Model,
    Stg: Strategy<S>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<S, M, Stg> Scheduler<S, M, Stg> for LIFO<S, M, Stg>
where
    S: Sequent,
    M: Model,
    Stg: Strategy<S>,
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
        r#impl::basic::{BasicEvaluator, BasicModel, BasicPreProcessor},
        strategy::Linear,
        PreProcessor, Scheduler,
    };
    use crate::test_prelude::*;
    use razor_fol::syntax::{Theory, FOF};
    use std::collections::HashSet;

    pub fn run(theory: &Theory<FOF>) -> Vec<BasicModel> {
        let pre_processor = BasicPreProcessor;
        let (sequents, init_model) = pre_processor.pre_process(theory);
        let evaluator = BasicEvaluator;
        let strategy: Linear<_> = sequents.iter().collect();
        let mut scheduler = LIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(init_model, strategy);
        chase_all(&mut scheduler, &evaluator, bounder)
    }

    #[test]
    fn test() {
        std::fs::read_dir("../theories/core")
            .unwrap()
            .map(|item| item.unwrap().path())
            .filter(|path| path.ends_with(".raz"))
            .for_each(|path| {
                let theory = read_theory_from_file(path.to_str().unwrap());
                let expected: HashSet<String> =
                    read_file(path.with_extension("model").to_str().unwrap())
                        .split("\n-- -- -- -- -- -- -- -- -- --\n")
                        .filter(|s| !s.is_empty())
                        .map(Into::into)
                        .collect();
                let result: HashSet<_> = run(&theory)
                    .into_iter()
                    .map(|m| print_basic_model(m))
                    .collect();
                assert_eq!(
                    expected,
                    result,
                    "invalid result for theory {}",
                    path.with_extension("").to_str().unwrap()
                );
            });
    }
}
