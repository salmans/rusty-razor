//! Provides a "basic" implementation of the chase.
//!
//! This implementation is used as a reference for the correctness of other implementations
//! of the [chase].
//!
//! **Note**: The performance of `chase::impl::basic` is not a concern.
//!
//! [chase]: crate::chase#the-chase
//!
use crate::chase::*;
use either::Either;
use itertools::Itertools;
use razor_fol::{
    syntax::{formula::Atomic, term::Complex, Formula, FOF},
    transform::GNF,
};
use std::{
    collections::{HashMap, HashSet},
    fmt, iter,
};

// Is a *positive* literal apearing in the body and the head of sequents
pub type Literal = Atomic<Complex>;

/// Is a straight forward implementation for [`WitnessTerm`], where elements are of type
/// [`E`].
///
/// [`WitnessTerm`]: crate::chase::WitnessTerm
/// [`E`]: crate::chase::E
#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum BasicWitnessTerm {
    /// Wraps an instance of [`E`], witnessing itself.
    ///
    /// [`E`]: crate::chase::E
    Elem(E),

    /// Wraps an instance of [`Const`] as a witness term.
    ///
    /// [`Const`]: razor_fol::syntax::Const
    Const(Const),

    /// Corresponds to a composite witness term, made by applying an instance of [`Func`]
    /// to a list of
    /// witness terms.
    ///
    /// [`Func`]: razor_fol::syntax::Func
    App { function: Func, terms: Vec<Self> },
}

impl BasicWitnessTerm {
    /// Given a `term` and an assignment function `assign` from variables of the term to elements
    /// of a [`Model`], constructs a [`WitnessTerm`].
    fn witness(term: &Complex, assign: &impl Fn(&Var) -> E) -> Self {
        match term {
            Complex::Const(c) => Self::Const(c.clone()),
            Complex::Var(v) => Self::Elem(assign(v)),
            Complex::App { function, terms } => {
                let terms = terms.iter().map(|t| Self::witness(t, assign)).collect();
                Self::App {
                    function: function.clone(),
                    terms,
                }
            }
        }
    }

    /// Builds a term by applying `function` on `args` as arguments.
    pub fn apply(function: Func, terms: Vec<Self>) -> Self {
        BasicWitnessTerm::App { function, terms }
    }
}

impl WitnessTerm for BasicWitnessTerm {
    type ElementType = E;
}

impl fmt::Display for BasicWitnessTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Elem(e) => write!(f, "{}", e),
            Self::Const(c) => write!(f, "{}", c),
            Self::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", function, ts.join(", "))
            }
        }
    }
}

impl fmt::Debug for BasicWitnessTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl From<Const> for BasicWitnessTerm {
    fn from(constant: Const) -> Self {
        Self::Const(constant)
    }
}

impl From<&Const> for BasicWitnessTerm {
    fn from(constant: &Const) -> Self {
        Self::from(constant.clone())
    }
}

impl From<E> for BasicWitnessTerm {
    fn from(element: E) -> Self {
        BasicWitnessTerm::Elem(element)
    }
}

impl From<&E> for BasicWitnessTerm {
    fn from(element: &E) -> Self {
        Self::from(*element)
    }
}

/// Is a basic instance of [`Model`] with terms of type [`WitnessTerm`].
///
/// [`Model`]: crate::chase::Model
pub struct BasicModel {
    /// Is a unique identifier for this model.
    id: u64,

    /// Keeps track of the next index to assign to a new element of this model.
    element_index: i32,

    /// Maps *flat* witness terms to elements of this model.
    ///
    /// **Hint**: Flat (witness) terms are terms that do not contain any composite sub-terms,
    /// consisting of functions applications.
    rewrites: HashMap<BasicWitnessTerm, E>,

    /// Contains a list of relational facts that are true in this model.
    facts: HashSet<Observation<BasicWitnessTerm>>,

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
    equality_history: HashMap<E, E>,
}

impl BasicModel {
    /// Creates a new empty instance of this model.
    pub fn new() -> Self {
        Self {
            id: rand::random(),
            element_index: 0,
            rewrites: HashMap::new(),
            facts: HashSet::new(),
            equality_history: HashMap::new(),
        }
    }

    /// Returns references to the elements of this model.
    fn domain_ref(&self) -> Vec<&E> {
        self.rewrites.values().into_iter().unique().collect()
    }

    /// Returns a reference to an element witnessed by the given witness term.
    fn element_ref(&self, witness: &BasicWitnessTerm) -> Option<&E> {
        match witness {
            BasicWitnessTerm::Elem(element) => {
                self.domain_ref().into_iter().find(|e| e.eq(&element))
            }
            BasicWitnessTerm::Const(_) => self.rewrites.get(witness),
            BasicWitnessTerm::App { function, terms } => {
                let terms: Vec<Option<&E>> = terms.iter().map(|t| self.element_ref(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    None
                } else {
                    let terms: Vec<BasicWitnessTerm> =
                        terms.into_iter().map(|e| (*e.unwrap()).into()).collect();
                    self.rewrites.get(&BasicWitnessTerm::App {
                        function: (*function).clone(),
                        terms,
                    })
                }
            }
        }
    }

    /// Applies the rewrite rules in `equality_history` of `self` to reduce an element to
    /// the representative element of the equational class to which it belongs.
    fn history(&self, element: &E) -> E {
        let mut result = element;
        let mut next;
        while {
            next = self.equality_history.get(result);
            next.is_some() && next.unwrap() != result
        } {
            result = next.unwrap()
        }

        *result
    }

    /// Creates a new element for the given `witness` and records that `witness` denotes the new
    /// element.
    fn new_element(&mut self, witness: BasicWitnessTerm) -> E {
        let element = E(self.element_index);
        self.element_index += 1;
        self.rewrites.insert(witness, element);
        element
    }

    /// Records the given `witness` in `self` and returns the element, denoted by
    /// `witness`.
    ///
    /// **Note**: `record` creates new elements that are denoted by `witness` and all sub-terms of
    /// `witness` and adds them to the domain of `self`.
    fn record(&mut self, witness: &BasicWitnessTerm) -> E {
        match witness {
            BasicWitnessTerm::Elem(element) => {
                let element = self.history(element);
                if self.domain().iter().any(|e| element.eq(e)) {
                    element
                } else {
                    unreachable!("missing element `{}`", element)
                }
            }
            BasicWitnessTerm::Const(_) => {
                if let Some(e) = self.rewrites.get(witness) {
                    *e
                } else {
                    self.new_element(witness.clone())
                }
            }
            BasicWitnessTerm::App { function, terms } => {
                let terms: Vec<BasicWitnessTerm> =
                    terms.iter().map(|t| self.record(t).into()).collect();
                let witness = BasicWitnessTerm::App {
                    function: function.clone(),
                    terms,
                };
                if let Some(e) = self.rewrites.get(&witness) {
                    *e
                } else {
                    self.new_element(witness)
                }
            }
        }
    }

    /// Replaces all instances of `from` with `to` in the `rewrite` of `self` and is used
    /// when augmenting the model with an `Identity` [`Observation`].
    ///
    /// **Note**: When augmenting a model with an `Identity`, we simply replace all instances of one
    /// side of the identity (i.e., the element denoted by one [witness term]) with the other
    /// one.
    ///
    /// [`Observation`]: crate::chase::Observation
    /// [witness term]: crate::chase::WitnessTerm
    fn reduce_rewrites(&mut self, from: &E, to: &E) {
        let mut new_rewrite: HashMap<BasicWitnessTerm, E> = HashMap::new();
        self.rewrites.iter().for_each(|(k, v)| {
            // k is a flat term and cannot be an element:
            let key = if let BasicWitnessTerm::App { function, terms } = k {
                let mut new_terms: Vec<BasicWitnessTerm> = Vec::new();
                terms.iter().for_each(|t| {
                    if let BasicWitnessTerm::Elem(element) = t {
                        if element == to {
                            new_terms.push(BasicWitnessTerm::Elem(*from));
                        } else {
                            new_terms.push(t.clone());
                        }
                    } else {
                        new_terms.push(t.clone());
                    }
                });
                BasicWitnessTerm::App {
                    function: function.clone(),
                    terms: new_terms,
                }
            } else {
                k.clone()
            };

            let value = if v == to { *from } else { *v };
            new_rewrite.insert(key, value);
        });
        self.rewrites = new_rewrite;
    }

    /// Replaces all instances of `from` with `to` in the `facts` of `self` and is used
    /// when augmenting the model with an `Identity` [`Observation`].
    ///
    /// **Note**: When augmenting a model with an identity, we simply replace all instances of one
    /// side of the identity (i.e., the element corresponding to its [witness term]) with the other
    /// one.
    ///
    /// [`Observation`]: crate::chase::Observation
    /// [witness term]: crate::chase::WitnessTerm
    fn reduce_facts(&mut self, from: &E, to: &E) {
        self.facts = self
            .facts
            .iter()
            .map(|f| {
                if let Observation::Fact {
                    ref relation,
                    ref terms,
                } = f
                {
                    let terms: Vec<BasicWitnessTerm> = terms
                        .iter()
                        .map(|t| {
                            if let BasicWitnessTerm::Elem(element) = t {
                                if element == to {
                                    (*from).into()
                                } else {
                                    (*t).clone()
                                }
                            } else {
                                (*t).clone() // should never happen
                            }
                        })
                        .collect();
                    Observation::Fact {
                        relation: relation.clone(),
                        terms,
                    }
                } else {
                    f.clone() // should never happen
                }
            })
            .collect();
    }

    /// Augments `self` with `observation`, making `observation` true in `self`.
    fn observe(&mut self, observation: &Observation<BasicWitnessTerm>) {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<BasicWitnessTerm> =
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
                let (from, to) = if left > right {
                    (right, left)
                } else {
                    (left, right)
                };

                // Since the underlying ElementType of the WitnessTerm, used for constructing this
                // type of model is not a reference to an object (unlike chase::impl::reference),
                // the following two steps are necessary to guarantee correctness:
                self.reduce_rewrites(&from, &to);
                self.reduce_facts(&from, &to);

                self.equality_history.insert(to, from);
            }
        }
    }

    /// Returns true if `observation` is true in `self`; otherwise, returns false.
    fn is_observed(&self, observation: &Observation<BasicWitnessTerm>) -> bool {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<Option<&E>> = terms.iter().map(|t| self.element_ref(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    false
                } else {
                    let terms: Vec<BasicWitnessTerm> =
                        terms.into_iter().map(|e| (*e.unwrap()).into()).collect();
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

impl Default for BasicModel {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for BasicModel {
    fn clone(&self) -> Self {
        Self {
            id: rand::random(),
            element_index: self.element_index,
            rewrites: self.rewrites.clone(),
            facts: self.facts.clone(),
            // In the `basic` implementation, a model is cloned after being processed in a
            // chase-step, so its `equality_history` does not need to persist after cloning it.
            equality_history: HashMap::new(),
        }
    }
}

impl Model for BasicModel {
    type TermType = BasicWitnessTerm;

    fn get_id(&self) -> u64 {
        self.id
    }

    fn domain(&self) -> Vec<E> {
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

    fn witness(&self, element: &E) -> Vec<BasicWitnessTerm> {
        self.rewrites
            .iter()
            .filter(|(_, e)| *e == element)
            .map(|(t, _)| t)
            .cloned()
            .collect()
    }

    fn element(&self, witness: &BasicWitnessTerm) -> Option<E> {
        self.element_ref(witness).cloned()
    }

    fn finalize(self) -> Self {
        self
    }
}

impl fmt::Debug for BasicModel {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let domain: Vec<String> = self.domain().into_iter().map(|e| e.to_string()).collect();
        let elements: Vec<String> = self
            .domain()
            .iter()
            .sorted()
            .iter()
            .map(|e| {
                let witnesses = self.witness(e).iter().map(|w| w.to_string()).sorted();
                format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e)
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

/// Is represented by a list of [`Literal`]s in the body and a list of list of `Literal`s in the
/// head.
#[derive(Clone)]
pub struct BasicSequent {
    /// Is the list of free variables in the sequent and is used for memoization.
    pub free_vars: Vec<Var>,

    /// Represents the body of the sequent as a list of [`Literal`]s. The literals in
    /// `body_literals` are assumed to be conjoined.
    ///
    /// **Note**: See [here](crate::chase#background) for more information about the structure
    /// of geometric sequents.
    pub body: Vec<Literal>,

    /// Represents the head of the sequent as a list of list of [`Literal`]s. The literals in
    /// each sublist of `head_literals` are assumed to be conjoined where the sublists are
    /// disjointed with each other.
    ///
    /// **Note**: See [here](crate::chase#background) for more information about the structure
    /// of geometric sequents.
    pub head: Vec<Vec<Literal>>,

    // other fields:
    body_fof: FOF,
    head_fof: FOF,
}

impl From<GNF> for BasicSequent {
    fn from(gnf: GNF) -> Self {
        let gnf_body = gnf.body();
        let gnf_head = gnf.head();
        let free_vars = gnf.free_vars().into_iter().cloned().collect();

        let body = gnf_body.iter().cloned().collect();
        let head = gnf_head
            .iter()
            .map(|h| h.iter().cloned().collect())
            .collect();

        Self {
            free_vars,
            body,
            head,
            body_fof: gnf_body.into(),
            head_fof: gnf_head.into(),
        }
    }
}

impl fmt::Display for BasicSequent {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let body: Vec<String> = self.body.iter().map(|l| l.to_string()).collect();
        let head: Vec<String> = self
            .head
            .iter()
            .map(|ls| {
                let ls: Vec<String> = ls.iter().map(|l| l.to_string()).collect();
                format!("[{}]", ls.join(", "))
            })
            .collect();
        write!(f, "[{}] -> [{}]", body.join(", "), head.join(", "))
    }
}

impl Sequent for BasicSequent {
    fn body(&self) -> FOF {
        self.body_fof.clone()
    }

    fn head(&self) -> FOF {
        self.head_fof.clone()
    }
}

/// A simple instance of [`PreProcessor`] that converts the input theory to a vector of [`Sequent`] following
/// the standard conversion to geometric normal form. Also provides the empty [`Model`];
///
/// [`PreProcessor`]: crate::chase::PreProcessor
pub struct BasicPreProcessor;

impl PreProcessor for BasicPreProcessor {
    type Sequent = BasicSequent;
    type Model = BasicModel;

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
            .map(BasicSequent::from)
            .collect();
        (geo_theory, BasicModel::new())
    }
}

/// Is a reference implementation of [`Evaluator`] for evaluating a basic [`Sequent`] in a basic [`Model`]
/// within a [chase-step].
///
/// [`Evaluator`]: crate::chase::Evaluator
/// [chase-step]: crate::chase#chase-step
pub struct BasicEvaluator;

impl<'s, Stg: Strategy<&'s BasicSequent>, B: Bounder> Evaluator<'s, Stg, B> for BasicEvaluator {
    type Sequent = BasicSequent;
    type Model = BasicModel;

    fn evaluate(
        &self,
        initial_model: &BasicModel,
        strategy: &mut Stg,
        bounder: Option<&B>,
    ) -> Option<EvaluateResult<BasicModel>> {
        let domain: Vec<&E> = initial_model.domain_ref().clone();
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
                let mut assignment_map: HashMap<&Var, E> = HashMap::new();
                for (i, item) in assignment.iter().enumerate().take(vars_size) {
                    assignment_map.insert(vars.get(i).unwrap(), *(*domain.get(*item).unwrap()));
                }
                // construct a "characteristic function" for the assignment map
                let assignment_func = |v: &Var| *assignment_map.get(v).unwrap();

                // lift the variable assignments to literals (used to create observations)
                let observe_literal = make_observe_literal(assignment_func);

                // build body and head observations
                let body: Vec<Observation<BasicWitnessTerm>> =
                    sequent.body.iter().map(&observe_literal).collect();
                let head: Vec<Vec<Observation<BasicWitnessTerm>>> = sequent
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
                    if head.is_empty() {
                        return None; // the chase fails if the head is empty (false)
                    } else {
                        // if there is a bounder, only extend models that are not out of the given bound:
                        let models: Vec<Either<BasicModel, BasicModel>> =
                            if let Some(bounder) = bounder {
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
    model: &'m BasicModel,
) -> impl FnMut(&'m Vec<Observation<BasicWitnessTerm>>) -> Either<BasicModel, BasicModel> {
    move |os: &'m Vec<Observation<BasicWitnessTerm>>| {
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
    model: &'m BasicModel,
) -> impl FnMut(&'m Vec<Observation<BasicWitnessTerm>>) -> Either<BasicModel, BasicModel> {
    move |os: &Vec<Observation<BasicWitnessTerm>>| {
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
    assignment_func: impl Fn(&Var) -> E,
) -> impl Fn(&Literal) -> Observation<BasicWitnessTerm> {
    move |lit: &Literal| match lit {
        Atomic::Atom(this) => {
            let terms = this
                .terms
                .iter()
                .map(|t| BasicWitnessTerm::witness(t, &assignment_func))
                .collect();
            Observation::Fact {
                relation: Rel::from(this.predicate.name()),
                terms,
            }
        }
        Atomic::Equals(this) => {
            let left = BasicWitnessTerm::witness(&this.left, &assignment_func);
            let right = BasicWitnessTerm::witness(&this.right, &assignment_func);
            Observation::Identity { left, right }
        }
    }
}

// Implements a counter to enumerate all the possible assignments of a domain of elements to free
// variables of a sequent. It mutates the given a list of indices, corresponding to mapping of each
// position to an element of a domain to the next assignment. Returns true if a next assignment
// exists and false otherwise.
fn next_assignment(vec: &mut [usize], last: usize) -> bool {
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

#[cfg(test)]
mod test_basic {
    use super::*;
    use crate::chase::{
        bounder::DomainSize, chase_all, scheduler::FIFO, strategy::Linear, Scheduler,
    };
    use crate::test_prelude::*;
    use razor_fol::transform::ToGNF;
    use std::iter::FromIterator;

    // Witness Elements
    pub fn _e_0() -> BasicWitnessTerm {
        e_0().into()
    }

    pub fn _e_1() -> BasicWitnessTerm {
        e_1().into()
    }

    pub fn _e_2() -> BasicWitnessTerm {
        e_2().into()
    }

    pub fn _e_3() -> BasicWitnessTerm {
        e_3().into()
    }

    pub fn _e_4() -> BasicWitnessTerm {
        e_4().into()
    }

    // Witness Constants
    pub fn _a_() -> BasicWitnessTerm {
        BasicWitnessTerm::Const(_a())
    }

    pub fn _b_() -> BasicWitnessTerm {
        BasicWitnessTerm::Const(_b())
    }

    pub fn _c_() -> BasicWitnessTerm {
        BasicWitnessTerm::Const(_c())
    }

    pub fn _d_() -> BasicWitnessTerm {
        BasicWitnessTerm::Const(_d())
    }

    #[test]
    fn test_witness_const() {
        assert_eq!(_a_(), _a().into());
        assert_eq!("'a", _a_().to_string());
    }

    #[test]
    fn test_observation() {
        assert_eq!("<R(e#0)>", _R_().app1(_e_0()).to_string());
        assert_eq!(
            "<R(e#0, e#1, e#2)>",
            _R_().app3(_e_0(), _e_1(), _e_2()).to_string()
        );
        assert_eq!("<e#0 = e#1>", _e_0().equals(_e_1()).to_string());
    }

    #[test]
    fn test_empty_model() {
        let model = BasicModel::new();
        let empty_domain: Vec<E> = Vec::new();
        let empty_facts: Vec<Observation<BasicWitnessTerm>> = Vec::new();
        assert_eq!(empty_domain, model.domain());
        assert_eq_sets(&empty_facts, &model.facts());
    }

    #[test]
    fn test_witness_app() {
        let f_0 = BasicWitnessTerm::apply(f(), vec![]);
        assert_eq!("f()", f_0.to_string());
        assert_eq!(
            "f('c)",
            BasicWitnessTerm::apply(f(), vec![_c_()]).to_string()
        );
        let g_0 = BasicWitnessTerm::apply(g(), vec![]);
        assert_eq!(
            "f(g())",
            BasicWitnessTerm::apply(f(), vec![g_0]).to_string()
        );
        assert_eq!(
            "f('c, g('d))",
            BasicWitnessTerm::apply(f(), vec![_c_(), BasicWitnessTerm::apply(g(), vec![_d_()])])
                .to_string()
        );
    }

    #[test]
    fn test_observe() {
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app0());
            assert_eq_sets(
                &Vec::from_iter(vec![_R_().app0()].into_iter()),
                &model.facts(),
            );
            assert!(model.is_observed(&_R_().app0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app1(_c_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0()]), &model.domain());
            assert_eq_sets(
                &Vec::from_iter(vec![_R_().app1(_e_0())].into_iter()),
                &model.facts(),
            );
            assert!(model.is_observed(&_R_().app1(_c_())));
            assert!(model.is_observed(&_R_().app1(_e_0())));
            assert!(!model.is_observed(&_R_().app1(_e_1())));
            assert_eq_sets(&Vec::from_iter(vec![_c_()]), &model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_a_().equals(_b_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0()]), &model.domain());
            let empty_facts: Vec<Observation<BasicWitnessTerm>> = Vec::new();
            assert_eq_sets(&empty_facts, &model.facts());
            assert_eq_sets(&Vec::from_iter(vec![_a_(), _b_()]), &model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_a_().equals(_a_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0()]), &model.domain());
            let empty_facts: Vec<Observation<BasicWitnessTerm>> = Vec::new();
            assert_eq_sets(&empty_facts, &model.facts());
            assert_eq_sets(&Vec::from_iter(vec![_a_()]), &model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_P_().app1(_a_()));
            model.observe(&_Q_().app1(_b_()));
            model.observe(&_a_().equals(_b_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0()]), &model.domain());
            assert_eq_sets(
                &Vec::from_iter(vec![_P_().app1(_e_0()), _Q_().app1(_e_0())].into_iter()),
                &model.facts(),
            );
            assert!(model.is_observed(&_P_().app1(_e_0())));
            assert!(model.is_observed(&_P_().app1(_a_())));
            assert!(model.is_observed(&_P_().app1(_b_())));
            assert!(model.is_observed(&_Q_().app1(_e_0())));
            assert!(model.is_observed(&_Q_().app1(_a_())));
            assert!(model.is_observed(&_Q_().app1(_b_())));
            assert_eq_sets(&Vec::from_iter(vec![_a_(), _b_()]), &model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app1(BasicWitnessTerm::apply(f(), vec![_c_()])));
            assert_eq_sets(&Vec::from_iter(vec![e_0(), e_1()]), &model.domain());
            assert_eq_sets(
                &Vec::from_iter(vec![_R_().app1(_e_1())].into_iter()),
                &model.facts(),
            );
            assert!(model.is_observed(&_R_().app1(_e_1())));
            assert!(model.is_observed(&_R_().app1(BasicWitnessTerm::apply(f(), vec![_c_()]))));
            assert_eq_sets(&Vec::from_iter(vec![_c_()]), &model.witness(&e_0()));
            assert_eq_sets(
                &Vec::from_iter(vec![BasicWitnessTerm::apply(f(), vec![_e_0()])]),
                &model.witness(&e_1()),
            );
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app2(_a_(), _b_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0(), e_1()]), &model.domain());
            assert_eq_sets(
                &Vec::from_iter(vec![_R_().app2(_e_0(), _e_1())].into_iter()),
                &model.facts(),
            );
            assert!(model.is_observed(&_R_().app2(_e_0(), _e_1())));
            assert!(!model.is_observed(&_R_().app2(_e_0(), _e_0())));
            assert_eq_sets(&Vec::from_iter(vec![_a_()]), &model.witness(&e_0()));
            assert_eq_sets(&Vec::from_iter(vec![_b_()]), &model.witness(&e_1()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app2(
                BasicWitnessTerm::apply(f(), vec![_c_()]),
                BasicWitnessTerm::apply(g(), vec![BasicWitnessTerm::apply(f(), vec![_c_()])]),
            ));
            assert_eq_sets(&Vec::from_iter(vec![e_0(), e_1(), e_2()]), &model.domain());
            assert_eq_sets(
                &Vec::from_iter(vec![_R_().app2(_e_1(), _e_2())].into_iter()),
                &model.facts(),
            );
            assert!(model.is_observed(&_R_().app2(_e_1(), _e_2())));
            assert!(model.is_observed(&_R_().app2(
                BasicWitnessTerm::apply(f(), vec![_c_()]),
                BasicWitnessTerm::apply(g(), vec![BasicWitnessTerm::apply(f(), vec![_c_()])])
            )));
            assert!(model
                .is_observed(&_R_().app(vec![BasicWitnessTerm::apply(f(), vec![_c_()]), _e_2()])));
            assert_eq_sets(&Vec::from_iter(vec![_c_()]), &model.witness(&e_0()));
            assert_eq_sets(
                &Vec::from_iter(vec![BasicWitnessTerm::apply(f(), vec![_e_0()])]),
                &model.witness(&e_1()),
            );
            assert_eq_sets(
                &Vec::from_iter(vec![BasicWitnessTerm::apply(g(), vec![_e_1()])]),
                &model.witness(&e_2()),
            );
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app(vec![_a_(), _b_()]));
            model.observe(&_S_().app(vec![_c_(), _d_()]));
            assert_eq_sets(
                &Vec::from_iter(vec![e_0(), e_1(), e_2(), e_3()]),
                &model.domain(),
            );
            assert_eq_sets(
                &Vec::from_iter(
                    vec![_R_().app2(_e_0(), _e_1()), _S_().app2(_e_2(), _e_3())].into_iter(),
                ),
                &model.facts(),
            );
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app(vec![_a_(), BasicWitnessTerm::apply(f(), vec![_a_()])]));
            model.observe(&_S_().app(vec![_b_()]));
            model.observe(&_R_().app(vec![
                BasicWitnessTerm::apply(g(), vec![BasicWitnessTerm::apply(f(), vec![_a_()])]),
                _b_(),
            ]));
            model.observe(&_S_().app(vec![_c_()]));
            assert_eq_sets(
                &Vec::from_iter(vec![e_0(), e_1(), e_2(), e_3(), e_4()]),
                &model.domain(),
            );
            assert_eq_sets(
                &Vec::from_iter(
                    vec![
                        _R_().app2(_e_0(), _e_1()),
                        _S_().app1(_e_4()),
                        _S_().app1(_e_2()),
                        _R_().app2(_e_3(), _e_2()),
                    ]
                    .into_iter(),
                ),
                &model.facts(),
            );
        }
    }

    #[test]
    #[should_panic]
    fn test_observe_missing_element() {
        let mut model = BasicModel::new();
        model.observe(&_R_().app1(_e_0()));
    }

    // Assumes that `fof` is in GNF, so it converts to a single GNF
    fn sequents(gnfs: Vec<GNF>) -> Vec<BasicSequent> {
        gnfs.into_iter().map(BasicSequent::from).collect()
    }

    #[test]
    fn test_build_sequent() {
        assert_debug_string("[]", sequents("true -> true".parse::<FOF>().unwrap().gnf()));
        assert_debug_string(
            "[]",
            sequents("true -> true & true".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            "[]",
            sequents("true -> true | true".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            "[[] -> []]",
            sequents("true -> false".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            "[[] -> []]",
            sequents("true -> false & true".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            "[[] -> []]",
            sequents("true -> true & false".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            "[]",
            sequents("true -> true | false".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            "[]",
            sequents("true -> false | true".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            "[[P(x)] -> [[Q(x)]]]",
            sequents("P(x) -> Q(x)".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            // Note: only range restricted geometric formulae get contracted
            "[[P(x), Q(x)] -> [[Q(y)]]]",
            sequents("P(x) & Q(x) -> Q(y)".parse::<FOF>().unwrap().gnf()),
        );
        assert_debug_string(
            "[[P(x, z), Q(x)] -> [[Q(x)], [R(z)]], [P(x, z), Q(x)] -> [[Q(x)], [S(z)]]]",
            sequents(
                "P(x, z) & Q(x) -> Q(x) | (R(z) & S(z))"
                    .parse::<FOF>()
                    .unwrap()
                    .gnf(),
            ),
        );
        assert_debug_string(
"[[D(x, y, z)] -> [[P(x)], [P(y)], [P(z)]], [D(x, y, z)] -> [[P(x)], [P(y)], [Q(z)]], [D(x, y, z)] -> [[P(x)], [P(z)], [Q(y)]], [D(x, y, z)] -> [[P(x)], [Q(y)], [Q(z)]], [D(x, y, z)] -> [[P(y)], [P(z)], [Q(x)]], [D(x, y, z)] -> [[P(y)], [Q(x)], [Q(z)]], [D(x, y, z)] -> [[P(z)], [Q(x)], [Q(y)]], [D(x, y, z)] -> [[Q(x)], [Q(y)], [Q(z)]]]",
            sequents(
                "D(x, y, z) -> (P(x) & Q(x)) | (P(y) & Q(y)) | (P(z) & Q(z))"
                    .parse::<FOF>()
                    .unwrap()
                    .gnf(),
            ),
        );
    }

    fn run(theory: &Theory<FOF>) -> Vec<BasicModel> {
        let pre_processor = BasicPreProcessor;
        let (sequents, init_model) = pre_processor.pre_process(theory);

        let evaluator = BasicEvaluator;
        let strategy: Linear<_> = sequents.iter().collect();

        let mut scheduler = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        scheduler.add(init_model, strategy);
        chase_all(&mut scheduler, &evaluator, bounder)
    }

    fn run_domain_bounded(theory: &Theory<FOF>, bound: usize) -> Vec<BasicModel> {
        let pre_processor = BasicPreProcessor;
        let (sequents, init_model) = pre_processor.pre_process(theory);
        let evaluator = BasicEvaluator;
        let strategy: Linear<_> = sequents.iter().collect();
        let mut scheduler = FIFO::new();
        let bounder = DomainSize::from(bound);
        let bounder: Option<&DomainSize> = Some(&bounder);
        scheduler.add(init_model, strategy);
        chase_all(&mut scheduler, &evaluator, bounder)
    }

    #[test]
    fn test_core() {
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

    #[test]
    fn test_bounded() {
        std::fs::read_dir("../theories/bounded")
            .unwrap()
            .map(|item| item.unwrap().path())
            .filter(|path| path.ends_with(".raz"))
            .for_each(|path| {
                let theory = read_theory_from_file(path.to_str().unwrap());
                let config = read_file(path.with_extension("config").to_str().unwrap())
                    .parse::<usize>()
                    .unwrap();
                let expected: HashSet<String> =
                    read_file(path.with_extension("model").to_str().unwrap())
                        .split("\n-- -- -- -- -- -- -- -- -- --\n")
                        .filter(|s| !s.is_empty())
                        .map(Into::into)
                        .collect();
                let result: HashSet<_> = run_domain_bounded(&theory, config)
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
