//! Implements various strategies for selecting sequents in a chase-step.
//!
//! The strategies are instances of [`StrategyTrait`].
//!
//! [`StrategyTrait`]: ../trait.StrategyTrait.html
use crate::chase::{SequentTrait, StrategyTrait};
use razor_fol::syntax::Formula;

/// Starting from the first [sequent] returns the next sequent every time `Iterator::next()` is
/// called on this strategy.
///
/// [sequent]: ../trait.SequentTrait.html
pub struct Linear<'s, S: SequentTrait> {
    /// Is the list of all [sequents] in this strategy.
    ///
    /// [sequents]: ../trait.SequentTrait.html
    sequents: Vec<&'s S>,

    /// Is an internal index, keeping track of the next sequent to return.
    index: usize,
}

impl<'s, S: SequentTrait> StrategyTrait for Linear<'s, S> {
    fn new<I: IntoIterator<Item = Self::Item>>(sequents: I) -> Self {
        Linear {
            sequents: sequents.into_iter().collect(),
            index: 0,
        }
    }
}

impl<'s, S: SequentTrait> Iterator for Linear<'s, S> {
    type Item = &'s S;

    fn next(&mut self) -> Option<&'s S> {
        self.index += 1;
        self.sequents.get(self.index - 1).map(|i| *i)
    }
}

impl<'s, S: SequentTrait> Clone for Linear<'s, S> {
    fn clone(&self) -> Self {
        Self {
            sequents: self.sequents.clone(),
            index: 0,
        }
    }
}

/// Avoids starving [sequents] by doing a round robin. The internal state of the
/// strategy is preserved when cloned; thus, the cloned strategy preserves fairness.
///
/// [sequents]: ../trait.SequentTrait.html
pub struct Fair<'s, S: SequentTrait> {
    /// Is the list of all [sequents] in this strategy.
    ///
    /// [sequents]: ../trait.StrategyTrait.html
    sequents: Vec<&'s S>,

    /// Is an internal index, keeping track of the next sequent to return.
    index: usize,

    /// For this instance (clone) of strategy, keeps track of the index of the first sequent that
    /// was returned.
    start: usize,

    /// Is an internal flag to keep track of whether all sequents have been visited or not.
    full_circle: bool,
}

impl<'s, S: SequentTrait> StrategyTrait for Fair<'s, S> {
    fn new<I: IntoIterator<Item = Self::Item>>(sequents: I) -> Self {
        Fair {
            sequents: sequents.into_iter().collect(),
            index: 0,
            start: 0,
            full_circle: false,
        }
    }
}

impl<'s, S: SequentTrait> Iterator for Fair<'s, S> {
    type Item = &'s S;

    fn next(&mut self) -> Option<&'s S> {
        if self.sequents.len() == 0 || (self.index == self.start && self.full_circle) {
            return None;
        }
        self.full_circle = true;
        let result = self.sequents.get(self.index).map(|s| *s);
        self.index = (self.index + 1) % self.sequents.len();
        result
    }
}

impl<'s, S: SequentTrait> Clone for Fair<'s, S> {
    fn clone(&self) -> Self {
        Self {
            sequents: self.sequents.clone(),
            index: self.index,
            start: self.index,
            full_circle: false,
        }
    }
}

/// Behaves like the [strategy] that it wraps but chooses the initial [sequents] (sequents with
/// empty body) only once at the beginning.
///
/// [strategy]: ../trait.StrategyTrait.html
/// [sequents]: ../trait.SequentTrait.html
#[derive(Clone)]
pub struct Bootstrap<'s, S: SequentTrait, Stg: StrategyTrait<Item = &'s S>> {
    /// Keeps track of the initial [sequents] (sequents with empty body) internally.
    ///
    /// [sequents]: ../trait.SequentTrait.html
    initial_sequents: Vec<&'s S>,

    /// Is the underlying [strategy] wrapped inside this instance.
    ///
    /// [strategy]: ../trait.StrategyTrait.html
    strategy: Stg,
}

impl<'s, S: SequentTrait, Stg: StrategyTrait<Item = &'s S>> StrategyTrait
    for Bootstrap<'s, S, Stg>
{
    fn new<I: IntoIterator<Item = Self::Item>>(sequents: I) -> Self {
        let (initial_sequents, rest) = sequents
            .into_iter()
            .partition(|s| s.body() == Formula::Top && s.head().free_vars().is_empty());
        Bootstrap {
            initial_sequents,
            strategy: Stg::new(rest),
        }
    }
}

impl<'s, S: SequentTrait, Stg: StrategyTrait<Item = &'s S>> Iterator for Bootstrap<'s, S, Stg> {
    type Item = &'s S;

    fn next(&mut self) -> Option<&'s S> {
        if !self.initial_sequents.is_empty() {
            Some(self.initial_sequents.remove(0))
        } else {
            self.strategy.next()
        }
    }
}

#[cfg(test)]
mod test_fair {
    use crate::chase::{
        bounder::DomainSize,
        chase_all,
        r#impl::basic::{Evaluator, Model, PreProcessor},
        scheduler::FIFO,
        strategy::Fair,
        ModelTrait, PreProcessorEx, SchedulerTrait, StrategyTrait,
    };
    use crate::test_prelude::{read_theory_from_file, solve_basic};
    use itertools::Itertools;
    use razor_fol::syntax::Theory;
    use std::collections::HashSet;
    use std::fs;

    pub fn print_model(model: Model) -> String {
        let elements: Vec<String> = model
            .domain()
            .iter()
            .sorted()
            .iter()
            .map(|e| {
                let witnesses: Vec<String> =
                    model.witness(e).iter().map(|w| w.to_string()).collect();
                let witnesses = witnesses.into_iter().sorted();
                format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e)
            })
            .collect();
        let domain: Vec<String> = model.domain().iter().map(|e| e.to_string()).collect();
        let facts: Vec<String> = model.facts().iter().map(|e| e.to_string()).collect();
        format!(
            "Domain: {{{}}}\nFacts: {}\n{}",
            domain.into_iter().sorted().join(", "),
            facts.into_iter().sorted().join(", "),
            elements.join("\n")
        )
    }

    fn run_test(theory: &Theory) -> Vec<Model> {
        let preprocessor = PreProcessor;
        let sequents = preprocessor.pre_process(theory);
        let evaluator = Evaluator;
        let strategy = Fair::new(sequents.iter());
        let mut scheduler = FIFO::new();
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
            let basic_models: HashSet<String> =
                basic_models.into_iter().map(|m| print_model(m)).collect();
            let test_models: HashSet<String> =
                test_models.into_iter().map(|m| print_model(m)).collect();
            assert_eq!(basic_models, test_models);
        }
    }
}

#[cfg(test)]
mod test_bootstrap {
    use crate::chase::scheduler::FIFO;
    use crate::chase::{
        bounder::DomainSize,
        chase_all,
        r#impl::basic::{Evaluator, Model, PreProcessor, Sequent},
        strategy::{Bootstrap, Fair},
        PreProcessorEx, SchedulerTrait, StrategyTrait,
    };
    use crate::test_prelude::*;
    use razor_fol::syntax::Theory;
    use std::collections::HashSet;
    use std::fs;

    fn run_test(theory: &Theory) -> Vec<Model> {
        let pre_processor = PreProcessor;
        let sequents = pre_processor.pre_process(theory);
        let evaluator = Evaluator;
        let strategy: Bootstrap<Sequent, Fair<Sequent>> = Bootstrap::new(sequents.iter());
        let mut scheduler = FIFO::new();
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
