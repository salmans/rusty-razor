use crate::chase::{SelectorTrait, SequentTrait};
use crate::formula::syntax::Formula;

/// ### Linear
/// Goes through the list of all sequents from the start and returns the next sequent every time
/// `Iterator::next()` is called.
#[derive(Clone)]
pub struct Linear<S: SequentTrait> {
    sequents: Vec<S>,
}

impl<S: SequentTrait> SelectorTrait for Linear<S> {
    fn new(sequents: Vec<S>) -> Linear<S> {
        Linear { sequents }
    }
}

impl<S: SequentTrait> Iterator for Linear<S> {
    type Item = S;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if self.sequents.is_empty() {
            None
        } else {
            Some(self.sequents.remove(0))
        }
    }
}

/// ### Fair
/// Avoids starving sequents by doing a round robin on the sequents. The internal state of the
/// selector is preserved when cloned, so the cloned selector can preserve fairness.
pub struct Fair<S: SequentTrait> {
    sequents: Vec<S>,
    index: usize,
    start: usize,
    full_circle: bool,
}

impl<S: SequentTrait> SelectorTrait for Fair<S> {
    fn new(sequents: Vec<S>) -> Fair<S> {
        Fair { sequents, index: 0, start: 0, full_circle: false }
    }
}

impl<S: SequentTrait> Iterator for Fair<S> {
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

impl<S: SequentTrait> Clone for Fair<S> {
    fn clone(&self) -> Self {
        Fair {
            sequents: self.sequents.clone(),
            index: self.index,
            start: self.index,
            full_circle: false,
        }
    }
}

#[derive(Clone)]
pub struct Bootstrap<S: SequentTrait, Sel: SelectorTrait<Item=S>> {
    initial_sequents: Vec<S>,
    selector: Sel,
}

impl<S: SequentTrait, Sel: SelectorTrait<Item=S>> SelectorTrait for Bootstrap<S, Sel> {
    fn new(sequents: Vec<S>) -> Bootstrap<S, Sel> {
        let (initial_sequents, rest) = sequents.into_iter()
            .partition(|s| { s.body() == Formula::Top && s.head().free_vars().is_empty() });
        Bootstrap { initial_sequents, selector: Sel::new(rest) }
    }
}

impl<S: SequentTrait, Sel: SelectorTrait<Item=S>> Iterator for Bootstrap<S, Sel> {
    type Item = S;

    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if !self.initial_sequents.is_empty() {
            Some(self.initial_sequents.remove(0))
        } else {
            self.selector.next()
        }
    }
}

#[cfg(test)]
mod test_fair {
    use crate::formula::syntax::Theory;
    use crate::chase::selector::Fair;
    use crate::chase::strategy::FIFO;
    use crate::chase::solve_all;
    use crate::chase::bounder::DomainSize;
    use crate::chase::StrategyTrait;
    use crate::chase::SelectorTrait;
    use crate::chase::r#impl::basic::Model;
    use crate::chase::r#impl::basic::Sequent;
    use crate::chase::r#impl::basic::Evaluator;
    use crate::test_prelude::solve_basic;
    use crate::test_prelude::read_theory_from_file;
    use std::collections::HashSet;
    use std::fs;
    use crate::chase::ModelTrait;
    use itertools::Itertools;

    pub fn print_model(model: Model) -> String {
        let elements: Vec<String> = model.domain().iter().sorted().iter().map(|e| {
            let witnesses: Vec<String> = model.witness(e).iter().map(|w| w.to_string()).collect();
            let witnesses = witnesses.into_iter().sorted();
            format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e)
        }).collect();
        let domain: Vec<String> = model.domain().iter().map(|e| e.to_string()).collect();
        let facts: Vec<String> = model.facts().iter().map(|e| e.to_string()).collect();
        format!("Domain: {{{}}}\nFacts: {}\n{}",
                domain.into_iter().sorted().join(", "),
                facts.into_iter().sorted().join(", "),
                elements.join("\n"))
    }

    fn run_test(theory: &Theory) -> Vec<Model> {
        let geometric_theory = theory.gnf();
        let sequents: Vec<Sequent> = geometric_theory
            .formulas
            .iter()
            .map(|f| f.into()).collect();

        let evaluator = Evaluator {};
        let selector = Fair::new(sequents);
        let mut strategy = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        strategy.add(Model::new(), selector);
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

#[cfg(test)]
mod test_bootstrap {
    use crate::formula::syntax::Theory;
    use crate::chase::{StrategyTrait, SelectorTrait, r#impl::basic::{Model, Sequent, Evaluator}
                       , bounder::DomainSize, selector::{Bootstrap, Fair}, strategy::FIFO, solve_all};
    use crate::test_prelude::*;
    use std::collections::HashSet;
    use std::fs;

    fn run_test(theory: &Theory) -> Vec<Model> {
        let geometric_theory = theory.gnf();
        let sequents: Vec<Sequent> = geometric_theory
            .formulas
            .iter()
            .map(|f| f.into()).collect();

        let evaluator = Evaluator {};
        let selector: Bootstrap<Sequent, Fair<Sequent>> = Bootstrap::new(sequents);
        let mut strategy = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        strategy.add(Model::new(), selector);
        solve_all(Box::new(strategy), Box::new(evaluator), bounder)
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