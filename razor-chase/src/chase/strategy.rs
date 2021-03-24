//! Implements various strategies for selecting sequents in a chase-step.
//!
//! The strategies are instances of [`Strategy`].
//!
//! [`Strategy`]: crate::chase::Strategy
use crate::chase::{Sequent, Strategy};
use razor_fol::syntax::{Formula, FOF};
use std::iter::FromIterator;

/// Starting from the first [sequent] returns the next sequent every time `Iterator::next()` is
/// called on this strategy.
///
/// [sequent]: crate::chase::Sequent
pub struct Linear<S: Sequent> {
    /// Is the list of all [sequents] in this strategy.
    ///
    /// [sequents]: crate::chase::Sequent
    sequents: Vec<S>,

    /// Is an internal index, keeping track of the next sequent to return.
    index: usize,
}

impl<'s, S: Sequent> Linear<S> {
    #[inline(always)]
    fn reset(&mut self) {
        self.index = 0;
    }
}

impl<S: Sequent> Iterator for Linear<S> {
    type Item = S;

    fn next(&mut self) -> Option<S> {
        self.index += 1;
        self.sequents.get(self.index - 1).cloned()
    }
}

impl<'s, S: Sequent> Clone for Linear<S> {
    fn clone(&self) -> Self {
        Self {
            sequents: self.sequents.clone(),
            index: 0,
        }
    }
}

impl<S: Sequent> FromIterator<S> for Linear<S> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        Linear {
            sequents: iter.into_iter().collect(),
            index: 0,
        }
    }
}

/// Avoids starving [sequents] by doing a round robin. The internal state of the
/// strategy is preserved when cloned; thus, the cloned strategy preserves fairness.
///
/// [sequents]: crate::chase::Sequent
pub struct Fair<'s, S: Sequent> {
    /// Is the list of all [sequents] in this strategy.
    ///
    /// [sequents]: crate::chase::Strategy
    sequents: Vec<&'s S>,

    /// Is an internal index, keeping track of the next sequent to return.
    index: usize,

    /// For this instance (clone) of strategy, keeps track of the index of the first sequent that
    /// was returned.
    start: usize,

    /// Is an internal flag to keep track of whether all sequents have been visited or not.
    full_circle: bool,
}

impl<'s, S: Sequent> FromIterator<&'s S> for Fair<'s, S> {
    fn from_iter<T: IntoIterator<Item = &'s S>>(iter: T) -> Self {
        Fair {
            sequents: iter.into_iter().collect(),
            index: 0,
            start: 0,
            full_circle: false,
        }
    }
}

impl<'s, S: Sequent> Iterator for Fair<'s, S> {
    type Item = &'s S;

    fn next(&mut self) -> Option<&'s S> {
        if self.sequents.is_empty() || (self.index == self.start && self.full_circle) {
            return None;
        }
        self.full_circle = true;
        let result = self.sequents.get(self.index).cloned();
        self.index = (self.index + 1) % self.sequents.len();
        result
    }
}

impl<'s, S: Sequent> Clone for Fair<'s, S> {
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
/// [strategy]: crate::chase::Strategy
/// [sequents]: crate::chase::Sequent
#[derive(Clone)]
pub struct Bootstrap<S: Sequent, Stg: Strategy<S>> {
    /// Is the list of initial [sequents] (sequents with empty body).
    ///
    /// [sequents]: crate::chase::Sequent
    initial_sequents: Vec<S>,

    /// Is the underlying [strategy] wrapped by this instance.
    ///
    /// [strategy]: crate::chase::Strategy
    strategy: Stg,
}

impl<S: Sequent, Stg: Strategy<S>> FromIterator<S> for Bootstrap<S, Stg> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        let (initial_sequents, rest) = iter
            .into_iter()
            .partition(|s| s.body() == FOF::Top && s.head().free_vars().is_empty());

        Bootstrap {
            initial_sequents,
            strategy: rest.into_iter().collect(),
        }
    }
}

impl<S: Sequent, Stg: Strategy<S>> Iterator for Bootstrap<S, Stg> {
    type Item = S;

    fn next(&mut self) -> Option<S> {
        if !self.initial_sequents.is_empty() {
            Some(self.initial_sequents.remove(0))
        } else {
            self.strategy.next()
        }
    }
}

/// Behaves like its underlying [strategy] but prioritizes all failing [sequents] (sequents with
/// empty head) before returning the next (non-failing) sequent. By using this strategy, the chase
/// would drop an inconsistent model as soon as possible.
///
/// [strategy]: crate::chase::Strategy
/// [sequents]: crate::chase::Sequent
#[derive(Clone)]
pub struct FailFast<S: Sequent, Stg: Strategy<S>> {
    /// Keeps track of failing [sequents] (sequents with empty head) by a [`Linear`] strategy.
    ///
    /// [sequents]: crate::chase::Sequent
    fail_strategy: Linear<S>,

    /// Is the underlying [strategy] wrapped by this instance.
    ///
    /// [strategy]: crate::chase::Strategy
    strategy: Stg,
}

impl<S: Sequent, Stg: Strategy<S>> FromIterator<S> for FailFast<S, Stg> {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        let (fail_sequents, rest): (Vec<_>, _) =
            iter.into_iter().partition(|s| s.head() == FOF::Bottom);

        Self {
            fail_strategy: fail_sequents.into_iter().collect(),
            strategy: rest.into_iter().collect(),
        }
    }
}

impl<S: Sequent, Stg: Strategy<S>> Iterator for FailFast<S, Stg> {
    type Item = S;

    fn next(&mut self) -> Option<S> {
        self.fail_strategy.next().or_else(|| {
            self.fail_strategy.reset();
            self.strategy.next()
        })
    }
}

#[cfg(test)]
mod test_fair {
    use crate::chase::{
        bounder::DomainSize,
        chase_all,
        r#impl::basic::{BasicEvaluator, BasicModel, BasicPreProcessor},
        scheduler::FIFO,
        strategy::Fair,
        Model, PreProcessor, Scheduler,
    };
    use crate::test_prelude::{read_theory_from_file, solve_basic};
    use itertools::Itertools;
    use razor_fol::syntax::{Theory, FOF};
    use std::collections::HashSet;
    use std::fs;

    pub fn print_model(model: BasicModel) -> String {
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

    fn run_test(theory: &Theory<FOF>) -> Vec<BasicModel> {
        let preprocessor = BasicPreProcessor;
        let (sequents, init_model) = preprocessor.pre_process(theory);
        let evaluator = BasicEvaluator;
        let strategy: Fair<_> = sequents.iter().collect();
        let mut scheduler = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(init_model, strategy);
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
        r#impl::basic::{BasicEvaluator, BasicModel, BasicPreProcessor},
        strategy::{Bootstrap, Fair},
        PreProcessor, Scheduler,
    };
    use crate::test_prelude::*;
    use razor_fol::syntax::{Theory, FOF};
    use std::collections::HashSet;
    use std::fs;

    fn run_test(theory: &Theory<FOF>) -> Vec<BasicModel> {
        let pre_processor = BasicPreProcessor;
        let (sequents, init_model) = pre_processor.pre_process(theory);
        let evaluator = BasicEvaluator;
        let strategy: Bootstrap<_, Fair<_>> = sequents.iter().collect();
        let mut scheduler = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(init_model, strategy);
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

#[cfg(test)]
mod test_fail_fast {
    use crate::chase::scheduler::FIFO;
    use crate::chase::{
        bounder::DomainSize,
        chase_all,
        r#impl::basic::{BasicEvaluator, BasicModel, BasicPreProcessor},
        strategy::{FailFast, Fair},
        PreProcessor, Scheduler,
    };
    use crate::test_prelude::*;
    use razor_fol::syntax::{Theory, FOF};
    use std::collections::HashSet;
    use std::fs;

    fn run_test(theory: &Theory<FOF>) -> Vec<BasicModel> {
        let pre_processor = BasicPreProcessor;
        let (sequents, init_model) = pre_processor.pre_process(theory);
        let evaluator = BasicEvaluator;
        let strategy: FailFast<_, Fair<_>> = sequents.iter().collect();
        let mut scheduler = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(init_model, strategy);
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
