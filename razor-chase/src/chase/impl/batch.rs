//! Improves `collapse` by evaluating the sequent provided by the strategy
//! against all assignments from the free variables of the sequent to the elements of the
//! model in which it is being evaluated.
//!
//! [`ColEvaluator`] extends the [`Model`] that it processes in a [chase-step]
//! only for one assignment from the free variables of the [`Sequent`] that it is
//! evaluating to the elements of the [`Model`]. [`BatchEvaluator`] is the only
//! different component between [`collapse`] and [`batch`] implementations.
//!
//! [`collapse`]: crate::chase::impl::collapse
//! [`Sequent`]: crate::chase::impl::basic::BasicSequent
//! [chase-step]: crate::chase#chase-step
//! [`Model`]: crate::chase::impl::collapse::ColModel
//! [`ColEvaluator`]: crate::chase::impl::collapse::ColEvaluator
//! [`batch`]: self

use crate::chase::{
    r#impl::{
        basic, collapse,
        collapse::{ColWitnessTerm, Element},
    },
    Bounder, EvaluateResult, Evaluator, Observation, Rel, Strategy,
};
use either::Either;
use itertools::Itertools;
use razor_fol::syntax::{formula::Atomic, Var};
use std::{collections::HashMap, iter};

/// Simple evaluator that evaluates a Sequnet in a Model.
pub struct BatchEvaluator;

impl<'s, Stg: Strategy<&'s BatchSequent>, B: Bounder> Evaluator<'s, Stg, B> for BatchEvaluator {
    type Sequent = BatchSequent;
    type Model = BatchModel;

    fn evaluate(
        &self,
        initial_model: &BatchModel,
        strategy: &mut Stg,
        bounder: Option<&B>,
    ) -> Option<EvaluateResult<BatchModel>> {
        let mut result = EvaluateResult::new();

        let domain: Vec<&Element> = initial_model.domain_ref();
        let domain_size = domain.len();
        for sequent in strategy {
            let vars = &sequent.free_vars;
            let vars_size = vars.len();
            if domain_size == 0 && vars_size > 0 {
                continue; // empty models can only be extended with sequents with no free variables.
            }

            // maintain a list of indices into the model elements to which variables are mapped
            let mut assignment: Vec<usize> = iter::repeat(0).take(vars_size).collect();

            // try all the variable assignments to the elements of the model
            // (notice the do-while pattern)
            while {
                // construct a map from variables to elements
                let mut assignment_map: HashMap<&Var, Element> = HashMap::new();
                for (i, item) in assignment.iter().enumerate() {
                    assignment_map
                        .insert(vars.get(i).unwrap(), (*domain.get(*item).unwrap()).clone());
                }
                // construct a "characteristic function" for the assignment map
                let assignment_func = |v: &Var| assignment_map.get(v).unwrap().clone();

                // lift the variable assignments to literals (used to make observations)
                let observe_literal = make_observe_literal(assignment_func);

                // build body and head observations
                let body = sequent.body.iter().map(&observe_literal).collect_vec();
                let head = sequent
                    .head
                    .iter()
                    .map(|l| l.iter().map(&observe_literal).collect_vec())
                    .collect_vec();

                // if all body observations are true in the model but not all the head observations
                // are true, extend the model:
                if body.iter().all(|o| initial_model.is_observed(o))
                    && !head
                        .iter()
                        .any(|os| os.iter().all(|o| initial_model.is_observed(o)))
                {
                    if head.is_empty() {
                        return None; // the chase fails if the head is empty (FALSE)
                    } else {
                        if result.open_models.is_empty() {
                            result.open_models.push(initial_model.clone());
                        }

                        // extending all extensions of this model with the new observations:
                        let models = result.open_models.into_iter().flat_map::<Vec<_>, _>(|m| {
                            if let Some(bounder) = bounder {
                                let extend = make_bounded_extend(bounder, &m);
                                head.iter().map(extend).collect()
                            } else {
                                let extend = make_extend(&m);
                                head.iter().map(extend).collect()
                            }
                        });

                        // all previous extensions are now extended further. so remove them from
                        // the result:
                        result.open_models = vec![];
                        models.for_each(|m| result.append(m));
                    }
                }

                // try the next variable assignment
                domain_size > 0 && next_assignment(&mut assignment, domain_size - 1)
            } {}
        }

        Some(result)
    }
}

// Returns a closure that returns a cloned extension of the given model, extended by a given set of
// observations.
fn make_extend<'m>(
    model: &'m BatchModel,
) -> impl FnMut(&'m Vec<Observation<ColWitnessTerm>>) -> Either<BatchModel, BatchModel> {
    move |os: &'m Vec<Observation<ColWitnessTerm>>| {
        let mut model = model.clone();
        os.iter().foreach(|o| model.observe(o));
        Either::Left(model)
    }
}

// Returns a closure that returns a cloned extension of the given model, extended by a given set of
// observations. Unlike `make_extend`, `make_bounded_extend` extends the model with respect to a
// bounder: a model wrapped in `Either::Right` has not reached the bounds while a model wrapped in
// `Either::Left` has reached the bounds provided by `bounder`.
fn make_bounded_extend<'m, B: Bounder>(
    bounder: &'m B,
    model: &'m BatchModel,
) -> impl FnMut(&'m Vec<Observation<ColWitnessTerm>>) -> Either<BatchModel, BatchModel> {
    move |os: &Vec<Observation<ColWitnessTerm>>| {
        let mut model = model.clone();
        let mut modified = false;
        os.iter().foreach(|o| {
            if bounder.bound(&model, o) {
                if !model.is_observed(o) {
                    modified = true;
                }
            } else if !model.is_observed(o) {
                model.observe(o);
            }
        });
        if modified {
            Either::Right(model)
        } else {
            Either::Left(model)
        }
    }
}

// Given an function from variables to elements of a model, returns a closure that lift the variable
// assignments to literals of a sequent, returning observations.
fn make_observe_literal(
    assignment_func: impl Fn(&Var) -> Element,
) -> impl Fn(&Literal) -> Observation<ColWitnessTerm> {
    move |lit: &Literal| match lit {
        Atomic::Atom(this) => {
            let terms = this
                .terms
                .iter()
                .map(|t| ColWitnessTerm::witness(t, &assignment_func))
                .collect();
            Observation::Fact {
                relation: Rel::from(this.predicate.name()),
                terms,
            }
        }
        Atomic::Equals(this) => {
            let left = ColWitnessTerm::witness(&this.left, &assignment_func);
            let right = ColWitnessTerm::witness(&this.right, &assignment_func);
            Observation::Identity { left, right }
        }
    }
}

// Implements a counter to enumerate all the possible assignments of a domain of elements to free
// variables of a sequent. It mutates the given a list of indices, corresponding to mapping of each
// position to an element of a domain to the next assignment. Returns true if a next assignment
// exists and false otherwise.
fn next_assignment(vec: &mut Vec<usize>, last: usize) -> bool {
    for item in vec.iter_mut() {
        if *item != last {
            *item += 1;
            return true;
        } else {
            *item = 0;
        }
    }
    false
}

pub type BatchSequent = basic::BasicSequent;
pub type BatchPreProcessor = collapse::ColPreProcessor;
pub type Literal = basic::Literal;
pub type BatchModel = collapse::ColModel;

#[cfg(test)]
mod test_batch {
    use super::{next_assignment, BatchEvaluator};
    use crate::chase::r#impl::collapse::ColModel;
    use crate::chase::{
        bounder::DomainSize, chase_all, scheduler::FIFO, strategy::Linear, Scheduler,
    };
    use crate::test_prelude::*;
    use razor_fol::syntax::{Theory, FOF};
    use std::collections::HashSet;

    static IGNORE_TEST: [&'static str; 1] = ["thy24.raz"];

    #[test]
    fn test_next_assignment() {
        {
            let mut assignment = vec![];
            assert_eq!(false, next_assignment(&mut assignment, 1));
            assert!(assignment.is_empty());
        }
        {
            let mut assignment = vec![0];
            assert_eq!(true, next_assignment(&mut assignment, 1));
            assert_eq!(vec![1], assignment);
        }
        {
            let mut assignment = vec![1];
            assert_eq!(false, next_assignment(&mut assignment, 1));
            assert_eq!(vec![0], assignment);
        }
        {
            let mut assignment = vec![0, 1];
            assert_eq!(true, next_assignment(&mut assignment, 1));
            assert_eq!(vec![1, 1], assignment);
        }
        {
            let mut assignment = vec![1, 1];
            assert_eq!(true, next_assignment(&mut assignment, 2));
            assert_eq!(vec![2, 1], assignment);
        }
        {
            let mut assignment = vec![2, 1];
            assert_eq!(true, next_assignment(&mut assignment, 2));
            assert_eq!(vec![0, 2], assignment);
        }
        {
            let mut assignment = vec![2, 2];
            assert_eq!(false, next_assignment(&mut assignment, 2));
            assert_eq!(vec![0, 0], assignment);
        }
        {
            let mut counter = 1;
            let mut vec = vec![0, 0, 0, 0, 0];
            while next_assignment(&mut vec, 4) {
                counter += 1;
            }
            assert_eq!(3125, counter);
        }
    }

    fn run(theory: &Theory<FOF>) -> Vec<ColModel> {
        use crate::chase::r#impl::collapse::ColPreProcessor;
        use crate::chase::PreProcessor;

        let pre_processor = ColPreProcessor;
        let (sequents, init_model) = pre_processor.pre_process(theory);

        let evaluator = BatchEvaluator;
        let strategy: Linear<_> = sequents.iter().collect();
        let mut scheduler = FIFO::new();
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
            .filter(|path| {
                IGNORE_TEST.contains(&path.file_name().and_then(|f| f.to_str()).unwrap())
            })
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
                    .map(|m| print_collapse_model(m))
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
