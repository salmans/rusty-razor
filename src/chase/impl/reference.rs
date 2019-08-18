use std::{
    rc::Rc,
    cell::Cell,
    fmt,
    collections::{HashMap, HashSet},
    iter,
    iter::FromIterator,
    hash::{Hash, Hasher},
    ops::Deref,
};
use crate::formula::syntax::{FuncApp, Term, V, C, Func};
use crate::chase::{r#impl::basic, E, Rel, Observation, WitnessTermTrait, ModelTrait, SelectorTrait, EvaluatorTrait, BounderTrait, ChaseStepResult};
use itertools::{Itertools, Either};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Element(Rc<Cell<E>>);

impl Element {
    fn new(element: E) -> Element {
        Element(Rc::new(Cell::new(element)))
    }

    fn deep_clone(&self) -> Self {
        Element::new(self.get())
    }
}

impl Hash for Element {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get().hash(state)
    }
}

impl Deref for Element {
    type Target = Rc<Cell<E>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Debug for Element {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.get().to_string())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WitnessTerm {
    Elem { element: Element },
    Const { constant: C },
    App { function: Func, terms: Vec<WitnessTerm> },
}

impl WitnessTerm {
    pub fn witness(term: &Term, lookup: &impl Fn(&V) -> Element) -> WitnessTerm {
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
    type ElementType = Element;
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

impl From<Element> for WitnessTerm {
    fn from(element: Element) -> Self {
        WitnessTerm::Elem { element }
    }
}

impl FuncApp for WitnessTerm {
    fn apply(function: Func, terms: Vec<Self>) -> Self {
        WitnessTerm::App { function, terms }
    }
}

pub struct Model {
    id: u64,
    element_index: i32,
    pub domain: HashSet<Element>,
    rewrites: HashMap<WitnessTerm, Element>,
    facts: HashSet<Observation<WitnessTerm>>,
    equality_history: HashMap<Element, Element>,
}

impl Model {
    pub fn new() -> Self {
        Self {
            id: rand::random(),
            element_index: 0,
            domain: HashSet::new(),
            rewrites: HashMap::new(),
            facts: HashSet::new(),
            equality_history: HashMap::new(),
        }
    }

    // Keeps track of the history of elements that are removed due to identifying with other
    // elements.
    // Under situations such as when there is an equation and a fact on the rhs of the same sequent,
    // the observation that is being observed might refer to a non-existing element.
    fn history(&self, element: &Element) -> Element {
        let mut result = element;
        let mut next;
        while {
            next = self.equality_history.get(result);
            next.is_some() && next.unwrap() != result
        } { result = next.unwrap() }

        result.clone()
    }

    #[inline]
    fn new_element(&mut self, witness: WitnessTerm) -> Element {
        let element = Element::new(E(self.element_index));
        self.element_index = self.element_index + 1;
        self.domain.insert(element.clone());
        self.rewrites.insert(witness, element.clone());
        element
    }

    fn record(&mut self, witness: &WitnessTerm) -> Element {
        match witness {
            WitnessTerm::Elem { element } => {
                let element = self.history(element);
                self.domain.iter().find(|e| element.eq(e)).unwrap().clone()
            }
            WitnessTerm::Const { .. } => {
                if let Some(e) = self.rewrites.get(&witness) {
                    e.clone()
                } else {
                    self.new_element(witness.clone())
                }
            }
            WitnessTerm::App { function, terms } => {
                let terms: Vec<WitnessTerm> = terms.into_iter().map(|t| self.record(t).into()).collect();
                let witness = WitnessTerm::App { function: function.clone(), terms };
                if let Some(e) = self.rewrites.get(&witness) {
                    (*e).clone()
                } else {
                    self.new_element(witness)
                }
            }
        }
    }
}

impl ModelTrait for Model {
    type TermType = WitnessTerm;

    fn get_id(&self) -> u64 { self.id }

    fn domain(&self) -> Vec<&Element> {
        self.domain.iter().sorted().into_iter().dedup().collect()
    }

    fn facts(&self) -> Vec<&Observation<Self::TermType>> {
        self.facts.iter().sorted().into_iter().dedup().collect()
    }

    fn observe(&mut self, observation: &Observation<Self::TermType>) {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<WitnessTerm> = terms.into_iter().map(|t| self.record(t).into()).collect();
                let observation = Observation::Fact { relation: relation.clone(), terms };
                self.facts.insert(observation);
            }
            Observation::Identity { left, right } => {
                let left = self.record(left);
                let right = self.record(right);
                let (src, dest) = if left > right {
                    (right, left)
                } else {
                    (left, right)
                };
                self.equality_history.insert(dest.deep_clone(), src.deep_clone());
                dest.replace(src.get());
            }
        }
    }

    fn is_observed(&self, observation: &Observation<Self::TermType>) -> bool {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<Option<&Element>> = terms.iter().map(|t| self.element(t)).collect();
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

    fn witness(&self, element: &Element) -> Vec<&Self::TermType> {
        self.rewrites.iter()
            .filter(|(_, e)| (*e).eq(element))
            .map(|(t, _)| t)
            .sorted()
            .into_iter()
            .dedup()
            .collect()
    }

    fn element(&self, witness: &Self::TermType) -> Option<&Element> {
        match witness {
            WitnessTerm::Elem { element } => {
                self.domain.iter().find(|e| e == &element)
            }
            WitnessTerm::Const { .. } => self.rewrites.get(witness),
            WitnessTerm::App { function, terms } => {
                let terms: Vec<Option<&Element>> = terms.iter().map(|t| self.element(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    None
                } else {
                    let terms: Vec<WitnessTerm> = terms.into_iter().map(|e| e.unwrap().clone().into()).collect();
                    self.rewrites.get(&WitnessTerm::App { function: (*function).clone(), terms })
                }
            }
        }
    }
}

impl Clone for Model {
    fn clone(&self) -> Self {
        let domain: HashSet<Element> = HashSet::from_iter(self.domain.iter().map(|e| e.deep_clone()));
        let map_element = |e: &Element| domain.get(e).unwrap().clone();
        let map_term = |w: &WitnessTerm| {
            match w {
                WitnessTerm::Elem { element } => WitnessTerm::Elem { element: map_element(element) },
                WitnessTerm::Const { .. } => w.clone(),
                WitnessTerm::App { function, terms } => {
                    let terms = terms.iter().map(|t| {
                        if let WitnessTerm::Elem { element } = t {
                            WitnessTerm::Elem { element: map_element(element) }
                        } else {
                            panic!("something is wrong: expecting an element")
                        }
                    }).collect();
                    WitnessTerm::App {
                        function: function.clone(),
                        terms,
                    }
                }
            }
        };
        let map_observation = |o: &Observation<WitnessTerm>| {
            if let Observation::Fact { relation, terms } = o {
                Observation::Fact {
                    relation: relation.clone(),
                    terms: terms.iter().map(|t| map_term(t)).collect(),
                }
            } else {
                panic!("something is wrong: expecting a fact")
            }
        };
        let rewrites: HashMap<WitnessTerm, Element> = HashMap::from_iter(self.rewrites.iter().map(|(k, v)| {
            (map_term(k), map_element(v))
        }));
        let facts: HashSet<Observation<WitnessTerm>> = HashSet::from_iter(self.facts.iter().map(|o| map_observation(o)));
        Model {
            id: rand::random(),
            element_index: self.element_index,
            domain,
            rewrites,
            facts,
            equality_history: self.equality_history.clone(),
        }
    }
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let domain: Vec<String> = self.domain().into_iter().map(|e| e.get().to_string()).collect();
        let elements: Vec<String> = self.domain().iter().sorted().iter().map(|e| {
            let witnesses: Vec<String> = self.witness(e).iter().map(|w| w.to_string()).collect();
            let witnesses = witnesses.into_iter().sorted();
            format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e.get())
        }).collect();
        let facts: Vec<String> = self.facts().into_iter().map(|e| e.to_string()).collect();
        write!(f, "Domain: {{{}}}\nElements:{}\nFacts: {}\n",
               domain.join(", "),
               elements.join(", "),
               facts.join(", "))
    }
}

/// Simple evaluator that evaluates a Sequnet in a Model.
pub struct Evaluator {}

impl<'s, Sel: SelectorTrait<Item=&'s Sequent>, B: BounderTrait> EvaluatorTrait<'s, Sel, B> for Evaluator {
    type Sequent = Sequent;
    type Model = Model;
    fn evaluate(
        &self,
        initial_model: &Model,
        selector: &mut Sel,
        bounder: Option<&B>
    ) -> Option<ChaseStepResult<Model>> {
        let domain: Vec<&Element> = initial_model.domain();
        let domain_size = domain.len();
        for sequent in selector {
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
                let mut assignment_map: HashMap<&V, Element> = HashMap::new();
                for i in 0..vars_size {
                    assignment_map.insert(vars.get(i).unwrap(), (*domain.get(assignment[i]).unwrap()).clone());
                }
                // construct a "characteristic function" for the assignment map
                let assignment_func = |v: &V| assignment_map.get(v).unwrap().clone();

                // lift the variable assignments to literals (used to make observations)
                let observe_literal = make_observe_literal(assignment_func);

                // build body and head observations
                let body: Vec<Observation<WitnessTerm>> = sequent.body_literals
                    .iter()
                    .map(&observe_literal)
                    .collect();
                let head: Vec<Vec<Observation<WitnessTerm>>> = sequent.head_literals
                    .iter()
                    .map(|l| l.iter().map(&observe_literal).collect())
                    .collect();

                // if all body observations are true in the model but not all the head observations
                // are true, extend the model:
                if body.iter().all(|o| initial_model.is_observed(o))
                    && !head.iter().any(|os| os.iter().all(|o| initial_model.is_observed(o))) {
                    info!(event = crate::trace::EVALUATE, sequent = %sequent,mapping = ?assignment_map);

                    if head.is_empty() {
                        return None; // the chase fails if the head is empty (FALSE)
                    } else {
                        // if there is a bounder, only extend models that are not out of the given bound:
                        let models: Vec<Either<Model, Model>> = if let Some(bounder) = bounder {
                            let extend = make_bounded_extend(bounder, initial_model);
                            head.iter().map(extend).collect()
                        } else {
                            let extend = make_extend(initial_model);
                            head.iter().map(extend).collect()
                        };

                        let result = ChaseStepResult::from(models);
                        if !result.is_empty() {
                            // this evaluator instantiates the first matching sequent with the first
                            // matching assignment (unlike impl::batch.rs)
                            return Some(result);
                        }
                    }
                }

                // try the next variable assignment
                domain_size > 0 && next_assignment(&mut assignment, domain_size - 1)
            } {}
        }
        Some(ChaseStepResult::new()) // if none of the assignments apply, the model is complete already
    }
}

// Returns a closure that returns a cloned extension of the given model, extended by a given set of
// observations.
#[inline]
fn make_extend<'m>(
    model: &'m Model
) -> impl FnMut(&'m Vec<Observation<WitnessTerm>>) -> Either<Model, Model>
{
    move |os: &'m Vec<Observation<WitnessTerm>>| {
        let mut model = model.clone();
        os.iter().foreach(|o| model.observe(o));
        Either::Left(model)
    }
}

// Returns a closure that returns a cloned extension of the given model, extended by a given set of
// observations. Unlike `make_extend`, `make_bounded_extend` extends the model with respect to a
// bounder: a model wrapped in `Either::Right` has not reached the bounds while a model wrapped in
// `Either::Left` has reached the bounds provided by `bounder`.
#[inline]
fn make_bounded_extend<'m, B: BounderTrait>(
    bounder: &'m B,
    model: &'m Model,
) -> impl FnMut(&'m Vec<Observation<WitnessTerm>>) -> Either<Model, Model>
{
    move |os: &Vec<Observation<WitnessTerm>>| {
        let mut model = model.clone();
        let mut modified = false;
        os.iter().foreach(|o| {
            if bounder.bound(&model, o) {
                if !model.is_observed(o) {
                    modified = true;
                }
            } else {
                if !model.is_observed(o) {
                    model.observe(o);
                }
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
#[inline]
fn make_observe_literal(assignment_func: impl Fn(&V) -> Element)
    -> impl Fn(&Literal) -> Observation<WitnessTerm> {
    move |lit: &Literal| {
        match lit {
            basic::Literal::Atm { predicate, terms } => {
                let terms = terms
                    .into_iter()
                    .map(|t| WitnessTerm::witness(t, &assignment_func))
                    .collect();
                Observation::Fact { relation: Rel(predicate.0.clone()), terms }
            }
            basic::Literal::Eql { left, right } => {
                let left = WitnessTerm::witness(left, &assignment_func);
                let right = WitnessTerm::witness(right, &assignment_func);
                Observation::Identity { left, right }
            }
        }
    }
}

// Implements a counter to enumerate all the possible assignments of a domain of elements to free
// variables of a sequent. It mutates the given a list of indices, corresponding to mapping of each
// position to an element of a domain to the next assignment. Returns true if a next assignment
// exists and false otherwise.
#[inline]
fn next_assignment(vec: &mut Vec<usize>, last: usize) -> bool {
    let len = vec.len();
    for i in 0..len {
        if vec[i] != last {
            vec[i] += 1;
            return true;
        } else {
            vec[i] = 0;
        }
    }
    false
}

pub type Sequent = basic::Sequent;
pub type Literal = basic::Literal;

#[cfg(test)]
mod test_reference {
    use super::{Model, Sequent, Evaluator, next_assignment};
    use crate::formula::syntax::Theory;
    use crate::chase::{StrategyTrait, SelectorTrait, selector::{Bootstrap, Fair}
                       , strategy::FIFO, bounder::DomainSize, solve_all};
    use crate::test_prelude::*;
    use std::collections::HashSet;
    use std::fs;

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