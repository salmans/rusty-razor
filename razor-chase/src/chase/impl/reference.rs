//! Provides a fast implementation of the Chase by using references to elements of the model to
//! avoid additional operations for equational reasoning.
//!
//! `chase::impl::reference` is an implementation of the [Chase] that uses references to [`E`]
//! wrapped in [`Element`] as the [`Model`] elements. Using object references allows for a faster
//! equational reasoning where the information content of a model does not need to be rewritten
//! ([as in `basic`][basic]) when the model is augmented by an [`Identity`].
//!
//! [Chase]: ../../index.html#the-chase
//! [`E`]: ../../struct.E.html
//! [`Element`]: ./struct.Element.html
//! [`Model`]: ./struct.Model.html
//! [`Identity`]: ../../enum.Observation.html#variant.Identity
//! [basic]: ../basic/struct.Model.html#method.reduce_rewrites
use crate::chase::{
    r#impl::basic, BounderTrait, EvaluateResult, EvaluatorTrait, ModelTrait, Observation, Rel,
    StrategyTrait, WitnessTermTrait, E,
};
use itertools::{Either, Itertools};
use razor_fol::syntax::{FApp, Term, C, F, V};
use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    fmt,
    hash::{Hash, Hasher},
    iter,
    iter::FromIterator,
    ops::Deref,
    rc::Rc,
};

/// Wraps a reference to [`E`] as the underlying [`ElementType`] of [`WitnessTerm`], used in the
/// implementation of [`Model`].
///
/// [`E`]: ../../struct.E.html
/// [`ElementType`]: ../../trait.WitnessTermTrait.html#associatedtype.ElementType
/// [`WitnessTerm`]: ./enum.WitnessTerm.html
/// [`Model`]: ./struct.Model.html
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Element(Rc<Cell<E>>);

impl Element {
    /// Creates a deep clone of the receiver by cloning the object [`E`] to which the internal
    /// reference is pointing.
    ///
    /// **Note**: `deep_copy` is used when cloning a [`Model`] since identifying two elements in the
    /// cloned model should not affect the original model and vise versa.
    ///
    /// [`E`]: ../../struct.E.html
    /// [`Model`]: ./struct.Model.html
    fn deep_clone(&self) -> Self {
        Element::from(self.get())
    }
}

impl From<E> for Element {
    fn from(e: E) -> Self {
        Self(Rc::new(Cell::new(e)))
    }
}

impl Hash for Element {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get().hash(state)
    }
}

// `Element` derefs to its underlying `E`
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

/// Implements [`WitnessTermTrait`], with [`Element`] as the [`ElementType`] and serves as witness
/// terms for [`Model`].
///
/// [`WitnessTermTrait`]: ../../trait.WitnessTermTrait.html
/// [`Element`]: ./struct.Element.html
/// [`ElementType`]: ../../trait.WitnessTermTrait.html#associatedtype.ElementType
/// [`Model`]: ./struct.Model.html
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WitnessTerm {
    /// Wraps an instance of [`Element`], witnessing itself.
    ///
    /// [`Element`]: ./struct.Element.html
    Elem { element: Element },

    /// Wraps an instance of [`C`] as a witness term.
    ///
    /// [`C`]: ../../../formula/syntax/struct.C.html
    Const { constant: C },

    /// Corresponds to a composite witness term, made by applying an instance of [`F`] to a list of
    /// witness terms.
    ///
    /// [`F`]: ../../../formula/syntax/struct.F.html
    App {
        function: F,
        terms: Vec<WitnessTerm>,
    },
}

impl WitnessTerm {
    /// Given a `term` and an assignment function `assign` from variables of the term to elements
    /// of a [`Model`], constructs a [`WitnessTerm`].
    ///
    /// [`WitnessTerm`]: ./enum.WitnessTerm.html
    /// [`Model`]: ./struct.Model.html
    pub fn witness(term: &Term, lookup: &impl Fn(&V) -> Element) -> WitnessTerm {
        match term {
            Term::Const { constant } => WitnessTerm::Const {
                constant: constant.clone(),
            },
            Term::Var { variable } => WitnessTerm::Elem {
                element: lookup(&variable),
            },
            Term::App { function, terms } => {
                let terms = terms
                    .iter()
                    .map(|t| WitnessTerm::witness(t, lookup))
                    .collect();
                WitnessTerm::App {
                    function: function.clone(),
                    terms,
                }
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

impl FApp for WitnessTerm {
    fn apply(function: F, terms: Vec<Self>) -> Self {
        WitnessTerm::App { function, terms }
    }
}

/// Is an instance of [`ModelTrait`] with terms of type [`WitnessTerm`], using references to [`E`]
/// wrapped in objects of type [`Element`] for efficient equational reasoning.
///
/// [`ModelTrait`]: ../../trait.ModelTrait.html
/// [`WitnessTerm`]: ./enum.WitnessTerm.html
/// [`E`]: ../../struct.E.html
/// [`Element`]: ./struct.Element.html
pub struct Model {
    /// Is a unique identifier for this model.
    id: u64,

    /// Keeps track of the next index to assign to a new element of this model.
    element_index: i32,

    /// Is the domain of this model, storing all elements of the model.
    pub domain: HashSet<Element>,

    /// Maps *flat* witness terms to elements of this model.
    ///
    /// **Hint**: Flat (witness) terms are terms that do not contain any composite sub-terms,
    /// consisting of functions applications.
    rewrites: HashMap<WitnessTerm, Element>,

    /// Contains a list of relational facts that are true in this model.
    facts: HashSet<Observation<WitnessTerm>>,

    /// Maintains a list of rewrite rules from elements to elements with which they have been
    /// identified.
    ///
    /// **Explanation**: When augmenting a model with a list of [observations] (such as observations
    /// that come from the head of a sequent being evaluated), identity observations are
    /// augmented by collapsing elements, that is, removing one element in favor of the other one.
    /// However, other augmenting observations may still point to an element that was removed as a
    /// result of augmenting an `Identity` observation.
    ///
    /// `equality_history` is used to keep track of identifications of elements temporarily during
    /// the time a model is being augmented in a [chase-step]. `equality_history` in a model becomes
    /// outdated after the [chase-step] ends.
    ///
    /// [observations]: ../../enum.Observation.html
    /// [chase-step]: ../../index.html#chase-step
    equality_history: HashMap<Element, Element>,
}

impl Model {
    /// Creates a new empty instance of this model.
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

    /// Applies the rewrite rules in `equality_history` of the receiver to reduce an element to
    /// the representative element of the equational class to which it belongs.
    fn history(&self, element: &Element) -> Element {
        let mut result = element;
        let mut next;
        while {
            next = self.equality_history.get(result);
            next.is_some() && next.unwrap() != result
        } {
            result = next.unwrap()
        }

        result.clone()
    }

    /// Creates a new element for the given `witness`, appends the element to the domain of the
    /// model and records that `witness` denotes the new element.
    fn new_element(&mut self, witness: WitnessTerm) -> Element {
        let element = Element::from(E(self.element_index));
        self.element_index = self.element_index + 1;
        self.domain.insert(element.clone());
        self.rewrites.insert(witness, element.clone());
        element
    }

    /// Records the given `witness` in the receiver model and returns the element, denoted by
    /// `witness`.
    ///
    /// **Note**: `record` creates new elements that are denoted by `witness` and all sub-terms of
    /// `witness` and adds them to the domain of the receiver.
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
                let terms: Vec<WitnessTerm> =
                    terms.into_iter().map(|t| self.record(t).into()).collect();
                let witness = WitnessTerm::App {
                    function: function.clone(),
                    terms,
                };
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

    fn get_id(&self) -> u64 {
        self.id
    }

    fn domain(&self) -> Vec<&Element> {
        self.domain.iter().unique().collect()
    }

    fn facts(&self) -> Vec<&Observation<Self::TermType>> {
        self.facts.iter().sorted().into_iter().dedup().collect()
    }

    fn observe(&mut self, observation: &Observation<Self::TermType>) {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<WitnessTerm> =
                    terms.into_iter().map(|t| self.record(t).into()).collect();
                let observation = Observation::Fact {
                    relation: relation.clone(),
                    terms,
                };
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
                self.equality_history
                    .insert(dest.deep_clone(), src.deep_clone());
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
                    let terms: Vec<WitnessTerm> = terms
                        .into_iter()
                        .map(|e| e.unwrap().clone().into())
                        .collect();
                    let obs = Observation::Fact {
                        relation: relation.clone(),
                        terms,
                    };
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
        self.rewrites
            .iter()
            .filter(|(_, e)| (*e).eq(element))
            .map(|(t, _)| t)
            .sorted()
            .into_iter()
            .dedup()
            .collect()
    }

    fn element(&self, witness: &Self::TermType) -> Option<&Element> {
        match witness {
            WitnessTerm::Elem { element } => self.domain.iter().find(|e| e == &element),
            WitnessTerm::Const { .. } => self.rewrites.get(witness),
            WitnessTerm::App { function, terms } => {
                let terms: Vec<Option<&Element>> = terms.iter().map(|t| self.element(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    None
                } else {
                    let terms: Vec<WitnessTerm> = terms
                        .into_iter()
                        .map(|e| e.unwrap().clone().into())
                        .collect();
                    self.rewrites.get(&WitnessTerm::App {
                        function: (*function).clone(),
                        terms,
                    })
                }
            }
        }
    }
}

impl Clone for Model {
    fn clone(&self) -> Self {
        let domain: HashSet<Element> =
            HashSet::from_iter(self.domain.iter().map(|e| e.deep_clone()));
        let map_element = |e: &Element| domain.get(e).unwrap().clone();
        let map_term = |w: &WitnessTerm| match w {
            WitnessTerm::Elem { element } => WitnessTerm::Elem {
                element: map_element(element),
            },
            WitnessTerm::Const { .. } => w.clone(),
            WitnessTerm::App { function, terms } => {
                let terms = terms
                    .iter()
                    .map(|t| {
                        if let WitnessTerm::Elem { element } = t {
                            WitnessTerm::Elem {
                                element: map_element(element),
                            }
                        } else {
                            panic!("something is wrong: expecting an element")
                        }
                    })
                    .collect();
                WitnessTerm::App {
                    function: function.clone(),
                    terms,
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
        let rewrites: HashMap<WitnessTerm, Element> = HashMap::from_iter(
            self.rewrites
                .iter()
                .map(|(k, v)| (map_term(k), map_element(v))),
        );
        let facts: HashSet<Observation<WitnessTerm>> =
            HashSet::from_iter(self.facts.iter().map(|o| map_observation(o)));
        Model {
            id: rand::random(),
            element_index: self.element_index,
            domain,
            rewrites,
            facts,
            // Because in the `chase::impl::batch` implementation, a model may be cloned multiple
            // times during a chase step, `equality_history` needs to be cloned as well.
            equality_history: self.equality_history.clone(),
        }
    }
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let domain: Vec<String> = self
            .domain()
            .into_iter()
            .map(|e| e.get().to_string())
            .collect();
        let elements: Vec<String> = self
            .domain()
            .iter()
            .sorted()
            .iter()
            .map(|e| {
                let witnesses: Vec<String> =
                    self.witness(e).iter().map(|w| w.to_string()).collect();
                let witnesses = witnesses.into_iter().sorted();
                format!(
                    "{} -> {}",
                    witnesses.into_iter().sorted().join(", "),
                    e.get()
                )
            })
            .collect();
        let facts: Vec<String> = self.facts().into_iter().map(|e| e.to_string()).collect();
        write!(
            f,
            "Domain: {{{}}}\nElements:{}\nFacts: {}\n",
            domain.join(", "),
            elements.join(", "),
            facts.join(", ")
        )
    }
}

/// Evaluates a [`Sequent`] in a [`Model`] within a [chase-step].
///
/// [`Sequent`]: ./struct.Sequent.html
/// [`Model`]: ./struct.Model.html
/// [chase-step]: ../../index.html#chase-step
pub struct Evaluator {}

impl<'s, Stg: StrategyTrait<Item = &'s Sequent>, B: BounderTrait> EvaluatorTrait<'s, Stg, B>
    for Evaluator
{
    type Sequent = Sequent;
    type Model = Model;
    fn evaluate(
        &self,
        initial_model: &Model,
        strategy: &mut Stg,
        bounder: Option<&B>,
    ) -> Option<EvaluateResult<Model>> {
        let domain: Vec<&Element> = initial_model.domain();
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
                let mut assignment_map: HashMap<&V, Element> = HashMap::new();
                for i in 0..vars_size {
                    assignment_map.insert(
                        vars.get(i).unwrap(),
                        (*domain.get(assignment[i]).unwrap()).clone(),
                    );
                }
                // construct a "characteristic function" for the assignment map
                let assignment_func = |v: &V| assignment_map.get(v).unwrap().clone();

                // lift the variable assignments to literals (used to make observations)
                let observe_literal = make_observe_literal(assignment_func);

                // build body and head observations
                let body: Vec<Observation<WitnessTerm>> =
                    sequent.body_literals.iter().map(&observe_literal).collect();
                let head: Vec<Vec<Observation<WitnessTerm>>> = sequent
                    .head_literals
                    .iter()
                    .map(|l| l.iter().map(&observe_literal).collect())
                    .collect();

                // if all body observations are true in the model but not all the head observations
                // are true, extend the model:
                if body.iter().all(|o| initial_model.is_observed(o))
                    && !head
                        .iter()
                        .any(|os| os.iter().all(|o| initial_model.is_observed(o)))
                {
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

                        let result = EvaluateResult::from(models);
                        if !result.empty() {
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
        Some(EvaluateResult::new()) // if none of the assignments apply, the model is complete already
    }
}

// Returns a closure that returns a cloned extension of the given model, extended by a given set of
// observations.
fn make_extend<'m>(
    model: &'m Model,
) -> impl FnMut(&'m Vec<Observation<WitnessTerm>>) -> Either<Model, Model> {
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
fn make_bounded_extend<'m, B: BounderTrait>(
    bounder: &'m B,
    model: &'m Model,
) -> impl FnMut(&'m Vec<Observation<WitnessTerm>>) -> Either<Model, Model> {
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
fn make_observe_literal(
    assignment_func: impl Fn(&V) -> Element,
) -> impl Fn(&Literal) -> Observation<WitnessTerm> {
    move |lit: &Literal| match lit {
        basic::Literal::Atm { predicate, terms } => {
            let terms = terms
                .into_iter()
                .map(|t| WitnessTerm::witness(t, &assignment_func))
                .collect();
            Observation::Fact {
                relation: Rel(predicate.0.clone()),
                terms,
            }
        }
        basic::Literal::Eql { left, right } => {
            let left = WitnessTerm::witness(left, &assignment_func);
            let right = WitnessTerm::witness(right, &assignment_func);
            Observation::Identity { left, right }
        }
    }
}

// Implements a counter to enumerate all the possible assignments of a domain of elements to free
// variables of a sequent. It mutates the given a list of indices, corresponding to mapping of each
// position to an element of a domain to the next assignment. Returns true if a next assignment
// exists and false otherwise.
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

/// Is a type synonym for [`basic::Sequent`].
///
/// **Note**: [`chase::impl::reference`] uses the same sequent type as [`chase::impl::basic`].
///
/// [`basic::Sequent`]: ../basic/struct.Sequent.html
/// [`chase::impl::reference`]: ./index.html
/// [`chase::impl::basic`]: ../basic/index.html
pub type Sequent = basic::Sequent;

/// Is a type synonym for [`basic::Literal`].
///
/// **Note**: [`chase::impl::reference`] uses the same sequent type as [`chase::impl::basic`].
///
/// [`basic::Literal`]: ../basic/struct.Literal.html
/// [`chase::impl::reference`]: ./index.html
/// [`chase::impl::basic`]: ../basic/index.html
pub type Literal = basic::Literal;

#[cfg(test)]
mod test_reference {
    use super::{next_assignment, Evaluator, Model, Sequent};
    use crate::chase::{
        bounder::DomainSize,
        chase_all,
        scheduler::FIFO,
        strategy::{Bootstrap, Fair},
        SchedulerTrait, StrategyTrait,
    };
    use crate::test_prelude::*;
    use razor_fol::syntax::Theory;
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
        let sequents: Vec<Sequent> = geometric_theory.formulae.iter().map(|f| f.into()).collect();

        let evaluator = Evaluator {};
        let strategy: Bootstrap<Sequent, Fair<Sequent>> = Bootstrap::new(sequents.iter().collect());
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
                .map(|m| print_reference_model(m))
                .collect();
            assert_eq!(basic_models, test_models);
        }
    }
}
