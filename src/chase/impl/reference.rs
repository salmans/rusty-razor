use std::rc::Rc;
use std::cell::Cell;
use crate::formula::syntax::{FuncApp, Term, V, C, Func};
use crate::chase::{
    r#impl::basic
    , E, Rel, Observation, WitnessTermTrait, ModelTrait
    , SelectorTrait, EvaluatorTrait, BounderTrait};
use std::fmt;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use itertools::{Itertools, Either};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum WitnessTerm {
    Elem { element: Rc<Cell<E>> },
    Const { constant: C },
    App { function: Func, terms: Vec<WitnessTerm> },
}

impl WitnessTerm {
    fn witness(term: &Term, lookup: &impl Fn(&V) -> Rc<Cell<E>>) -> WitnessTerm {
        match term {
            Term::Const { constant } => WitnessTerm::Const { constant: constant.clone() },
            Term::Var { variable } => WitnessTerm::Elem { element: lookup(&variable) },
            Term::App { function, terms } => {
                let terms = terms.iter().map(|t| WitnessTerm::witness(t, lookup)).collect();
                WitnessTerm::App { function: function.clone(), terms }
            }
        }
    }
}

impl WitnessTermTrait for WitnessTerm {
    type ElementType = Rc<Cell<E>>;
}

impl fmt::Display for WitnessTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            WitnessTerm::Elem { element } => write!(f, "{}", element.get()),
            WitnessTerm::Const { constant } => write!(f, "{}", constant),
            WitnessTerm::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}[{}]", function, ts.join(", "))
            }
        }
    }
}

impl From<C> for WitnessTerm {
    fn from(constant: C) -> Self {
        WitnessTerm::Const { constant }
    }
}

impl From<Rc<Cell<E>>> for WitnessTerm {
    fn from(element: Rc<Cell<E>>) -> Self {
        WitnessTerm::Elem { element }
    }
}

impl From<E> for WitnessTerm {
    fn from(element: E) -> Self {
        WitnessTerm::Elem { element: Rc::new(Cell::new(element)) }
    }
}

impl FuncApp for WitnessTerm {
    fn apply(function: Func, terms: Vec<Self>) -> Self {
        WitnessTerm::App { function, terms }
    }
}

#[derive(Clone)]
pub struct Model {
    element_index: i32,
    domain: BTreeSet<Rc<Cell<E>>>,
    rewrites: BTreeMap<WitnessTerm, Rc<Cell<E>>>,
    facts: BTreeSet<Observation<WitnessTerm>>,
}

impl Model {
    pub fn new() -> Model {
        Model {
            element_index: 0,
            domain: BTreeSet::new(),
            rewrites: BTreeMap::new(),
            facts: BTreeSet::new(),
        }
    }

    fn record(&mut self, witness: WitnessTerm) -> Rc<Cell<E>> {
        match witness {
            WitnessTerm::Elem { element } => {
                if let Some(_) = self.domain.iter().find(|e| element.eq(e)) {
                    element
                } else {
                    panic!("Element does not exist in the model's domain!")
                }
            }
            WitnessTerm::Const { .. } => {
                if let Some(e) = self.rewrites.get(&witness) {
                    e.clone()
                } else {
                    let element = Rc::new(Cell::new(E(self.element_index)));
                    self.element_index = self.element_index + 1;
                    self.domain.insert(element.clone());
                    self.rewrites.insert(witness, element.clone());
                    element
                }
            }
            WitnessTerm::App { function, terms } => {
                let terms: Vec<WitnessTerm> = terms.into_iter().map(|t| self.record(t).into()).collect();
                let witness = WitnessTerm::App { function, terms };
                if let Some(e) = self.rewrites.get(&witness) {
                    (*e).clone()
                } else {
                    let element = Rc::new(Cell::new(E(self.element_index)));
                    self.element_index = self.element_index + 1;
                    self.domain.insert(element.clone());
                    self.rewrites.insert(witness, element.clone());
                    element
                }
            }
        }
    }
}

impl ModelTrait for Model {
    type TermType = WitnessTerm;

    fn domain(&self) -> Vec<&Rc<Cell<E>>> {
        self.domain.iter().sorted().into_iter().dedup().collect()
    }

    fn facts(&self) -> Vec<&Observation<Self::TermType>> {
        self.facts.iter().sorted().into_iter().dedup().collect()
    }

    fn observe(&mut self, observation: &Observation<Self::TermType>) {
        match observation {
            Observation::Fact { relation, terms } => {
                // TODO do we need the clone below?
                let terms: Vec<WitnessTerm> = terms.into_iter().map(|t| self.record((*t).clone()).into()).collect();
                let observation = Observation::Fact { relation: relation.clone(), terms };
                self.facts.insert(observation);
            }
            Observation::Identity { left, right } => {
                let left = self.record((*left).clone());
                let right = self.record((*right).clone());
                let (src, dest) = if left > right {
                    (right, left)
                } else {
                    (left, right)
                };
                self.rewrites.iter().for_each(|(_, v)| {
                    if v.eq(&dest) {
                        v.replace(src.get());
                        //v.get().identify(&src.get())
                    }
                });
            }
        }
    }

    fn is_observed(&self, observation: &Observation<Self::TermType>) -> bool {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<Option<&Rc<Cell<E>>>> = terms.iter().map(|t| self.element(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    false
                } else {
                    let terms: Vec<WitnessTerm> = terms.into_iter().map(|e| e.unwrap().clone().into()).collect();
                    let obs = Observation::Fact { relation: relation.clone(), terms };
                    self.facts.iter().find(|f| obs.eq(f)).is_some()
                }
            }
            Observation::Identity { left, right } => {
                let left = self.element(left);
                left.is_some() && left == self.element(right)
            }
        }
    }

    fn witness(&self, element: &Rc<Cell<E>>) -> Vec<&Self::TermType> {
        self.rewrites.iter()
            .filter(|(_, e)| (*e).eq(element))
            .map(|(t, _)| t)
            .sorted()
            .into_iter()
            .dedup()
            .collect()
    }

    fn element(&self, witness: &Self::TermType) -> Option<&Rc<Cell<E>>> {
        match witness {
            WitnessTerm::Elem { element } => {
                self.domain.iter().find(|e| (*e).eq(element))
            }
            WitnessTerm::Const { .. } => self.rewrites.get(witness),
            WitnessTerm::App { function, terms } => {
                let terms: Vec<Option<&Rc<Cell<E>>>> = terms.iter().map(|t| self.element(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    None
                } else {
                    let terms: Vec<WitnessTerm> = terms.into_iter().map(|e| e.unwrap().get().into()).collect();
                    self.rewrites.get(&WitnessTerm::App { function: (*function).clone(), terms })
                }
            }
        }
    }
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let domain: Vec<String> = self.domain().into_iter().map(|e| e.get().to_string()).collect();
        let facts: Vec<String> = self.facts().into_iter().map(|e| e.to_string()).collect();
        write!(f, "Domain: {{{}}}\nFacts: {}\n", domain.join(", "), facts.join(", "))
    }
}

/// Simple evaluator that evaluates a Sequnet in a Model.
pub struct Evaluator {}

impl<'s, Sel: SelectorTrait<Item=&'s Sequent>, B: BounderTrait> EvaluatorTrait<'s, Sel, B> for Evaluator {
    type Sequent = Sequent;
    type Model = Model;
    fn evaluate(&self, model: &Model, selector: &mut Sel, bounder: Option<&B>)
                -> Option<Vec<Either<Model, Model>>> {
        let domain: Vec<&Rc<Cell<E>>> = model.domain().into_iter().collect();
        let domain_size = domain.len();
        for sequent in selector {
            let sequent_vars = &sequent.free_vars;
            let sequent_size = sequent_vars.len();
            let end = usize::pow(domain_size, sequent_size as u32);
            for i in 0..end {
                let mut wit_map: HashMap<&V, Rc<Cell<E>>> = HashMap::new();
                let mut j: usize = 0;
                let mut total = i;
                while j < sequent_size {
                    wit_map.insert(sequent_vars.get(j).unwrap(), (*domain.get(total % domain_size).unwrap()).clone());
                    j += 1;
                    total /= domain_size;
                }
                let witness_func = |v: &V| wit_map.get(v).unwrap().clone();
                let convert = |lit: &Literal| {
                    match lit {
                        basic::Literal::Atm { predicate, terms } => {
                            let terms = terms.into_iter().map(|t| WitnessTerm::witness(t, &witness_func)).collect();
                            Observation::Fact { relation: Rel(predicate.0.clone()), terms }
                        }
                        basic::Literal::Eql { left, right } => {
                            let left = WitnessTerm::witness(left, &witness_func);
                            let right = WitnessTerm::witness(right, &witness_func);
                            Observation::Identity { left, right }
                        }
                    }
                };

                let body: Vec<Observation<WitnessTerm>> = sequent.body_literals.iter().map(convert).collect();
                let head: Vec<Vec<Observation<WitnessTerm>>> = sequent.head_literals.iter().map(|l| l.iter().map(convert).collect()).collect();

                if body.iter().all(|o| model.is_observed(o))
                    && !head.iter().any(|os| os.iter().all(|o| model.is_observed(o))) {
                    if head.is_empty() {
                        return None; // failure
                    } else {
                        let models: Vec<Either<Model, Model>> = head.iter().filter_map(|os| {
                            let mut model = model.clone();
                            // this evaluator returns the models from first successful sequent
                            if let Some(bounder) = bounder {
                                let mut modified = false;
                                os.iter().foreach(|o| {
                                    if !bounder.bound(&model, o) && !model.is_observed(o) {
                                        model.observe(o);
                                        modified = true;
                                    }
                                });
                                if modified {
                                    Some(Either::Right(model))
                                } else {
                                    None
                                }
                            } else {
                                os.iter().foreach(|o| model.observe(o));
                                Some(Either::Left(model))
                            }
                        }).collect();
                        if !models.is_empty() {
                            return Some(models);
                        }
                    }
                }
            }
        }
        return Some(Vec::new());
    }
}

pub type Sequent = basic::Sequent;
pub type Literal = basic::Literal;

#[cfg(test)]
mod test_bootstrap {
    use super::{Model, Evaluator};
    use crate::chase::r#impl::basic::Sequent;
    use crate::formula::syntax::Theory;
    use crate::chase::{StrategyTrait, SelectorTrait, selector::{Bootstrap, Fair}
                       , strategy::FIFO, bounder::DomainSize, solve_all};
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
        let selector: Bootstrap<Sequent, Fair<Sequent>> = Bootstrap::new(sequents.iter().collect());
        let mut strategy = FIFO::new();
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
            let test_models: HashSet<String> = test_models.into_iter().map(|m| print_reference_model(m)).collect();
            assert_eq!(basic_models, test_models);
        }
    }
}