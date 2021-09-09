//! Provides an implementation of the chase by collapsing references to elements
//! of the model to avoid equational reasoning computation.
//!
//! [`collapse`] is an implementation of the [chase] that uses references to [`E`]
//! wrapped in [`Element`] as the [`Model`] elements. Using object references allows for a
//! faster equational reasoning where the information content of a model does not need to
//! be rewritten when the model is augmented by an [`Identity`].
//!
//! [chase]: crate::chase#the-chase
//! [`Identity`]: crate::chase::Observation::Identity
//! [`collapse`]: self
use crate::chase::{
    r#impl::basic, Bounder, EvaluateResult, Evaluator, Model, Observation, PreProcessor, Rel,
    Strategy, WitnessTerm, E,
};
use either::Either;
use itertools::Itertools;
use razor_fol::syntax::{formula::Atomic, term::Complex, Const, Func, Theory, Var, FOF};
use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    fmt,
    hash::{Hash, Hasher},
    iter,
    ops::Deref,
    rc::Rc,
};

/// Wraps a reference to [`E`] as the underlying [`ElementType`] of [`WitnessTerm`], used in the
/// implementation of [`Model`].
///
/// [`E`]: crate::chase::E
/// [`ElementType`]: crate::chase::WitnessTerm::ElementType
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Element(Rc<Cell<E>>);

impl Element {
    /// Creates a deep clone of `self` by cloning the object [`E`] to which the internal
    /// reference is pointing.
    ///
    /// **Note**: `deep_copy` is used when cloning a [`Model`] since identifying two elements in the
    /// cloned model should not affect the original model and vise versa.
    ///
    /// [`E`]: crate::chase::E
    fn deep_clone(&self) -> Self {
        Element::from(self.get())
    }
}

impl From<E> for Element {
    fn from(e: E) -> Self {
        Self(Rc::new(Cell::new(e)))
    }
}

#[allow(clippy::derive_hash_xor_eq)]
impl Hash for Element {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get().hash(state)
    }
}

// `element` derefs to its underlying `E`
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

/// Implements [`WitnessTerm`], with [`Element`] as the [`ElementType`] and serves as witness
/// terms for [`Model`].
///
/// [`WitnessTerm`]: crate::chase::WitnessTerm
/// [`ElementType`]: crate::chase::WitnessTerm::ElementType
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ColWitnessTerm {
    /// Wraps an instance of [`Element`], witnessing itself.
    Elem(Element),

    /// Wraps an instance of [`Const`] as a witness term.
    ///
    /// [`Const`]: razor_fol::syntax::Const
    Const(Const),

    /// Corresponds to a composite witness term, made by applying an instance of [`Func`]
    /// to a list of
    /// witness terms.
    ///
    /// [`Func`]: razor_fol::syntax::Func
    App {
        function: Func,
        terms: Vec<ColWitnessTerm>,
    },
}

impl ColWitnessTerm {
    /// Given a `term` and an assignment function `assign` from variables of the term to elements
    /// of a [`Model`], constructs a [`WitnessTerm`].
    pub fn witness(term: &Complex, lookup: &impl Fn(&Var) -> Element) -> ColWitnessTerm {
        match term {
            Complex::Const(c) => ColWitnessTerm::Const(c.clone()),
            Complex::Var(v) => ColWitnessTerm::Elem(lookup(v)),
            Complex::App { function, terms } => {
                let terms = terms
                    .iter()
                    .map(|t| ColWitnessTerm::witness(t, lookup))
                    .collect();
                ColWitnessTerm::App {
                    function: function.clone(),
                    terms,
                }
            }
        }
    }
}

impl WitnessTerm for ColWitnessTerm {
    type ElementType = Element;
}

impl fmt::Display for ColWitnessTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ColWitnessTerm::Elem(e) => write!(f, "{}", e.get()),
            ColWitnessTerm::Const(c) => write!(f, "{}", c),
            ColWitnessTerm::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", function, ts.join(", "))
            }
        }
    }
}

impl From<Const> for ColWitnessTerm {
    fn from(constant: Const) -> Self {
        ColWitnessTerm::Const(constant)
    }
}

impl From<Element> for ColWitnessTerm {
    fn from(element: Element) -> Self {
        ColWitnessTerm::Elem(element)
    }
}

/// Is an instance of [`Model`] with terms of type [`WitnessTerm`], using references to [`E`]
/// wrapped in objects of type [`Element`] for efficient equational reasoning.
///
/// [`Model`]: crate::chase::Model
/// [`E`]: crate::chase::E
pub struct ColModel {
    /// Is a unique identifier for this model.
    id: u64,

    /// Keeps track of the next index to assign to a new element of this model.
    element_index: i32,

    /// Is the domain of this model, storing all elements of the model.
    pub domain: Vec<Element>,

    /// Maps *flat* witness terms to elements of this model.
    ///
    /// **Hint**: Flat (witness) terms are terms that do not contain any composite sub-terms,
    /// consisting of functions applications.
    rewrites: Vec<(ColWitnessTerm, Element)>,

    /// Contains a list of relational facts that are true in this model.
    facts: HashSet<Observation<ColWitnessTerm>>,

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
    /// [observations]: crate::chase::Observation
    /// [chase-step]: crate::chase#chase-step
    equality_history: HashMap<Element, Element>,
}

impl ColModel {
    /// Creates a new empty instance of this model.
    pub fn new() -> Self {
        Self {
            id: rand::random(),
            element_index: 0,
            domain: Vec::new(),
            rewrites: Vec::new(),
            facts: HashSet::new(),
            equality_history: HashMap::new(),
        }
    }

    /// Returns references to the elements of this model.
    pub fn domain_ref(&self) -> Vec<&Element> {
        self.domain.iter().unique().collect()
    }

    /// Looks up `element` in the `domain` of `self`.
    fn lookup_element(&self, element: &Element) -> Option<&Element> {
        self.domain.iter().find(|e| e == &element)
    }

    /// Looks up `witness` in the `rewrites` of `self`.
    fn lookup_witness(&self, witness: &ColWitnessTerm) -> Option<&Element> {
        self.rewrites
            .iter()
            .find(|&x| &x.0 == witness)
            .map(|x| &x.1)
    }

    /// Returns a reference to an element witnessed by the given witness term.
    fn element_ref(&self, witness: &ColWitnessTerm) -> Option<&Element> {
        match witness {
            ColWitnessTerm::Elem(e) => self.lookup_element(e),
            ColWitnessTerm::Const(_) => self.lookup_witness(witness),
            ColWitnessTerm::App { function, terms } => {
                let terms: Vec<Option<&Element>> =
                    terms.iter().map(|t| self.element_ref(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    None
                } else {
                    let terms: Vec<ColWitnessTerm> = terms
                        .into_iter()
                        .map(|e| e.unwrap().clone().into())
                        .collect();
                    let term = ColWitnessTerm::App {
                        function: (*function).clone(),
                        terms,
                    };
                    self.lookup_witness(&term)
                }
            }
        }
    }

    /// Applies the rewrite rules in `equality_history` of `self` to reduce an element to
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
    fn new_element(&mut self, witness: ColWitnessTerm) -> Element {
        let element = Element::from(E(self.element_index));
        self.element_index += 1;
        self.domain.push(element.clone());
        self.rewrites.push((witness, element.clone()));
        element
    }

    /// Records the given `witness` in `self` and returns the element, denoted by
    /// `witness`.
    ///
    /// **Note**: `record` creates new elements that are denoted by `witness` and all sub-terms of
    /// `witness` and adds them to the domain of `self`.
    fn record(&mut self, witness: &ColWitnessTerm) -> Element {
        match witness {
            ColWitnessTerm::Elem(e) => {
                let element = self.history(e);
                self.lookup_element(&element).unwrap().clone()
            }
            ColWitnessTerm::Const(_) => {
                if let Some(e) = self.lookup_witness(witness) {
                    e.clone()
                } else {
                    self.new_element(witness.clone())
                }
            }
            ColWitnessTerm::App { function, terms } => {
                let terms: Vec<ColWitnessTerm> =
                    terms.iter().map(|t| self.record(t).into()).collect();
                let witness = ColWitnessTerm::App {
                    function: function.clone(),
                    terms,
                };
                if let Some(e) = self.lookup_witness(&witness) {
                    e.clone()
                } else {
                    self.new_element(witness)
                }
            }
        }
    }

    /// Augments `self` with `observation`, making `observation`true in `self`.
    pub fn observe(&mut self, observation: &Observation<ColWitnessTerm>) {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<ColWitnessTerm> =
                    terms.iter().map(|t| self.record(t).into()).collect();
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

    /// Returns true if `observation` is true in `self`; otherwise, returns false.
    pub fn is_observed(&self, observation: &Observation<ColWitnessTerm>) -> bool {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<Option<&Element>> =
                    terms.iter().map(|t| self.element_ref(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    false
                } else {
                    let terms: Vec<ColWitnessTerm> = terms
                        .into_iter()
                        .map(|e| e.unwrap().clone().into())
                        .collect();
                    let obs = Observation::Fact {
                        relation: relation.clone(),
                        terms,
                    };
                    self.facts.iter().any(|f| obs.eq(f))
                }
            }
            Observation::Identity { left, right } => {
                let left = self.element(left);
                left.is_some() && left == self.element(right)
            }
        }
    }
}

impl Default for ColModel {
    fn default() -> Self {
        Self::new()
    }
}

impl Model for ColModel {
    type TermType = ColWitnessTerm;

    fn get_id(&self) -> u64 {
        self.id
    }

    fn domain(&self) -> Vec<Element> {
        self.domain_ref().into_iter().cloned().collect()
    }

    fn facts(&self) -> Vec<Observation<Self::TermType>> {
        self.facts
            .clone()
            .into_iter()
            .sorted()
            .into_iter()
            .dedup()
            .collect()
    }

    fn witness(&self, element: &Element) -> Vec<Self::TermType> {
        self.rewrites
            .iter()
            .filter(|(_, e)| (*e).eq(element))
            .map(|(t, _)| t)
            .sorted()
            .into_iter()
            .dedup()
            .cloned()
            .collect()
    }

    fn element(&self, witness: &Self::TermType) -> Option<Element> {
        self.element_ref(witness).cloned()
    }

    fn finalize(self) -> Self {
        self
    }
}

impl Clone for ColModel {
    fn clone(&self) -> Self {
        let domain: Vec<Element> = self.domain.iter().map(|e| e.deep_clone()).collect();
        let map_element = |e: &Element| domain.iter().find(|&x| x == e).unwrap().clone();
        let map_term = |w: &ColWitnessTerm| match w {
            ColWitnessTerm::Elem(e) => ColWitnessTerm::Elem(map_element(e)),
            ColWitnessTerm::Const(_) => w.clone(),
            ColWitnessTerm::App { function, terms } => {
                let terms = terms
                    .iter()
                    .map(|t| {
                        if let ColWitnessTerm::Elem(e) = t {
                            ColWitnessTerm::Elem(map_element(e))
                        } else {
                            unreachable!("expecting an element, found `{}`", t)
                        }
                    })
                    .collect();
                ColWitnessTerm::App {
                    function: function.clone(),
                    terms,
                }
            }
        };
        let map_observation = |o: &Observation<ColWitnessTerm>| {
            if let Observation::Fact { relation, terms } = o {
                Observation::Fact {
                    relation: relation.clone(),
                    terms: terms.iter().map(|t| map_term(t)).collect(),
                }
            } else {
                unreachable!("expecting a fact, found `{}`", o)
            }
        };
        let rewrites: Vec<(ColWitnessTerm, Element)> = self
            .rewrites
            .iter()
            .map(|(k, v)| (map_term(k), map_element(v)))
            .collect();

        let facts: HashSet<Observation<ColWitnessTerm>> =
            self.facts.iter().map(|o| map_observation(o)).collect();
        ColModel {
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

impl fmt::Debug for ColModel {
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

/// Is the [preprocessor] instance for this implementation.
///
/// [preprocessor]: crate::chase::PreProcessor
pub struct ColPreProcessor;

impl PreProcessor for ColPreProcessor {
    type Sequent = ColSequent;
    type Model = ColModel;

    fn pre_process(&self, theory: &Theory<FOF>) -> (Vec<Self::Sequent>, Self::Model) {
        use razor_fol::transform::ToGNF;
        use razor_fol::transform::ToSNF;

        let mut c_counter: u32 = 0;
        let mut f_counter: u32 = 0;
        let mut const_generator = || {
            let name = format!("c#{}", c_counter);
            c_counter += 1;
            name.into()
        };
        let mut fn_generator = || {
            let name = format!("f#{}", f_counter);
            f_counter += 1;
            name.into()
        };

        let geo_theory = theory
            .iter()
            .map(|f| f.snf_with(&mut const_generator, &mut fn_generator))
            .flat_map(|f| f.gnf())
            .map(ColSequent::from)
            .collect();
        (geo_theory, ColModel::new())
    }
}

/// Evaluates a [`ColSequent`] in a [`Model`] within a [chase-step].
///
/// [chase-step]: crate::chase#chase-step
pub struct ColEvaluator;

impl<'s, Stg: Strategy<&'s ColSequent>, B: Bounder> Evaluator<'s, Stg, B> for ColEvaluator {
    type Sequent = ColSequent;
    type Model = ColModel;

    fn evaluate(
        &self,
        initial_model: &ColModel,
        strategy: &mut Stg,
        bounder: Option<&B>,
    ) -> Option<EvaluateResult<ColModel>> {
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
                for (i, item) in assignment.iter().enumerate().take(vars_size) {
                    assignment_map
                        .insert(vars.get(i).unwrap(), (*domain.get(*item).unwrap()).clone());
                }
                // construct a "characteristic function" for the assignment map
                let assignment_func = |v: &Var| assignment_map.get(v).unwrap().clone();

                // lift the variable assignments to literals (used to make observations)
                let observe_literal = make_observe_literal(assignment_func);

                // build body and head observations
                let body: Vec<Observation<ColWitnessTerm>> =
                    sequent.body.iter().map(&observe_literal).collect();
                let head: Vec<Vec<Observation<ColWitnessTerm>>> = sequent
                    .head
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
                        let models: Vec<Either<ColModel, ColModel>> = if let Some(bounder) = bounder
                        {
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
    model: &'m ColModel,
) -> impl FnMut(&'m Vec<Observation<ColWitnessTerm>>) -> Either<ColModel, ColModel> {
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
    model: &'m ColModel,
) -> impl FnMut(&'m Vec<Observation<ColWitnessTerm>>) -> Either<ColModel, ColModel> {
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

/// Is a type synonym for [`basic::BasicSequent`].
///
/// **Note**: [`collapse`] uses the same sequent type as [`basic`].
///
/// [`basic::BasicSequent`]: crate::chase::impl::basic::BasicSequent
/// [`collapse`]: self
/// [`basic`]: crate::chase::impl::basic
pub type ColSequent = basic::BasicSequent;

/// Is a type synonym for [`basic::Literal`].
///
/// **Note**: [`collapse`] uses the same sequent type as [`basic`].
///
/// [`basic::Literal`]: crate::chase::impl::basic::Literal
/// [`collapse`]: self
/// [`basic`]: crate::chase::impl::basic
pub type Literal = basic::Literal;

#[cfg(test)]
mod test_collapse {
    use super::{next_assignment, ColEvaluator, ColModel};
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
        use crate::chase::PreProcessor;

        let pre_processor = super::ColPreProcessor;
        let (sequents, init_model) = pre_processor.pre_process(theory);

        let evaluator = ColEvaluator;
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
