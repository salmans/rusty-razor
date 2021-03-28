//! Provides a framework and interfaces to various components that are used for implementing
//! the chase. It also implements entrypoints for running the chase.
//!
//! ## Background
//! Razor implements a variant of [the chase] algorithm to construct models for first-order theories with
//! equality. The chase operates on *[geometric theories]*, theories that contain a syntactic
//! variation of first-order formulae which we refer to as the Geometric Normal Form (GNF). Formulae
//! in GNF have the following shape:
//!
//! A<sub>1</sub> ∧ ... ∧ A<sub>m</sub> →
//! (∃ x<sub>11</sub>, ..., x<sub>1j<sub>1</sub></sub> . A<sub>11</sub> ∧ ... ∧ A<sub>1n<sub>1</sub></sub>) </br>
//! > > &nbsp;&nbsp;&nbsp;
//! ∨ (∃ x<sub>21</sub>, ..., x<sub>2j<sub>2</sub></sub> . A<sub>21</sub> ∧ ... ∧ A<sub>2n<sub>2</sub></sub>) </br>
//! > > &nbsp;&nbsp;&nbsp;
//! ∨ ... </br>
//! > > &nbsp;&nbsp;&nbsp;
//! ∨ (∃ x<sub>i1</sub>, ..., x<sub>ij<sub>i</sub></sub> . A<sub>i1</sub> ∧ ... ∧ A<sub>in<sub>i</sub></sub>)
//!
//! where A<sub>k</sub>s are (positive) atomic formulae (possibly including equality) and free
//! variables are assumed to be universally qualified over the entire formula.
//!
//! In the context of a [run of the chase], we refer to formulae in the their GNF as
//! [*sequents*][Sequent]. The premise (left side) and the consequence (right side) of the
//! implication are respectively said to be the *body* and the *head* of the sequent.
//!
//! ### Satisfiability of Geometric Theories
//! It turns out that every first-order theory can be transformed to a geometric theory that is
//! *equisatisfiable* to the original theory via [standard syntactic manipulation].
//! In fact, for every model *N* of the original theory, there exists a model *M* of the geometric
//! theory such that there is a homomorphism from *M* to *N*. This is an important result that
//! enables Razor to utilize the chase to construct homomorphically minimal models of a given
//! first-order theory.
//!
//! In the context of a model-finding application, the models that the chase produces are desirable
//! since they contain minimum amount of information, thus they induce minimal distraction.
//! As a direct consequence of semi-decidability of satisfiability in first-order logic
//! (see [Gödel's incompleteness theorems][godel]), satisfiability of geometric theories is
//! semi-decidable as well.
//!
//! **Note**: A comprehensive discussion on the properties of the models that are constructed by
//! the chase is out of the scope of this document.
//!
//! [the chase]: https://en.wikipedia.org/wiki/Chase_(algorithm)
//! [geometric theories]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
//! [run of the chase]: self#chase_all
//! [standard syntactic manipulation]: razor_fol::transform::CNF::gnf()
//! [godel]: https://en.wikipedia.org/wiki/Gödel%27s_incompleteness_theorems
//!
//! ## The Chase
//! Given a geometric theory and starting with an empty model, a run of the chase consists of repeated
//! applications of [chase-step]s by which the model is augmented with *necessary* pieces of
//! information until there is a contradiction or the model satisfies the theory. Within
//! Razor's implementation, instances of any type that implements [Model] can serve as a
//! first-order model. Also, inspired by [Steven Vickers][vickers], we refer to the units of
//! information that augment models as [observation][Observation]s.
//!
//! [chase-step]: self#chase-step
//! [vickers]: https://www.cs.bham.ac.uk/~sjv/GeoZ.pdf
//!
//! ### Chase Step
//! Given a geometric theory and an existing model, a chase-step proceeds as follows:
//!
//! 1. A sequent from the theory is selected to be evaluated against the model. Razor uses an
//! instance of [Strategy] to select the sequent.
//!
//! 2. The selected sequent is evaluated against the model: given an assignment from the free
//! variables of the sequent to the elements of the model, if the body of the sequent is true and
//! its head is not true in the model, new observations are added to the model to make the
//! sequent's head true. Instances of any type that implements [Evaluator] may be used to
//! evaluate the sequent in the model.
//!
//!     2.1. If the sequent is headless, meaning its consequence is falsehood (an empty disjunction),
//! the chase fails on the given model.
//!
//!     2.2. If the head of the sequent contains more than one disjunct (with at least one
//! non-trivial disjunction), the chase branches and satisfies each disjunct independently on clones
//! of the model. Razor uses instances of [Scheduler] to schedule various branches of the chase
//! for future chase steps.
//!
//!     2.3. If no sequent can be found such that its body and head are respectively true and false
//! in the model, the model already satisfies the theory and will be returned as an output of
//! the chase.
//!
//! ### Termination
//! As a result of semi-decidability of geometric theories, it can be shown if a geometric theory
//! is unsatisfiable, a run of the chase on the theory always terminates, although it may take
//! a very very long time.
//! However, when the theory is satisfiable, a run of the chase may not terminate, producing
//! infinitely large models and/or infinitely many models that satisfy the theory. Nevertheless,
//! in practice, Razor can *bound* the size of models created by the chase to guarantee termination.
//! Razor uses instances of types that implement [Bounder] to implement various strategies to
//! cap the size of search space for models.
//!
//! ## Implementation
//! The primary motivation for implementing Razor is to study the chase and improve its performance
//! for practical applications. The flexible (but somehow complex) design of Razor allows for
//! experimenting with various data structures to represent [models][Model] and
//! [sequents][Sequent], [evaluating][Evaluator] sequents in models using a variety
//! of algorithms, testing different ideas for [scheduling][Scheduler] branches of
//! the chase and devising various [strategies][Strategy] for selecting sequents. Also,
//! because of theoretical and non-theoretical consequences of non-termination of the chase,
//! Razor is going to explore a variety of ideas for limiting the search space by
//! [bounding][Bounder] the size of models:
//!
//! Interesting combinations of these various options are constantly benchmarked and the
//! configuration with the best average performance is used by the Rusty Razor application.
//!
pub mod bounder;
pub mod r#impl;
pub mod scheduler;
pub mod strategy;

use razor_fol::syntax::*;
use std::{fmt, iter::FromIterator};

use either::Either;

/// Is a symbol to represent elements of first-order models. An element is identified by an index.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct E(pub i32);

impl E {
    /// Identifies `self` with `other` element by collapsing their indices.
    /// ```rust
    /// # use razor_chase::chase::E;
    /// let mut e_1 = E::from(1);
    /// let e_2 = E::from(2);
    /// assert_ne!(e_1, e_2);
    ///
    /// e_1.identify(&e_2);
    /// assert_eq!(e_1, e_2);
    /// ```
    pub fn identify(&mut self, other: &Self) {
        self.0 = other.0;
    }
}

impl From<i32> for E {
    fn from(i: i32) -> Self {
        E(i)
    }
}

impl fmt::Display for E {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "e#{}", self.0)
    }
}

impl fmt::Debug for E {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Is the trait for special kind of variable-free terms that are used to witness existence of
/// model elements. These terms are used as provenance information for models to describe *why*
/// elements exist or facts are true in models.
pub trait WitnessTerm: Clone + PartialEq + Eq + fmt::Display {
    /// Is the type of elements that are witnessed by the witness term.
    ///
    /// **Note**: Although [`E`] is often the underlying symbol for representing elements,
    /// models may implement their own element types based on or independent from `E`.
    /// See [`ColModel`](self::impl::collapse::ColModel) for an example.
    type ElementType;

    /// Returns an equational [`Observation`] between `self` and the give witness term.
    fn equals(self, rhs: Self) -> Observation<Self> {
        Observation::Identity {
            left: self,
            right: rhs,
        }
    }
}

/// Relations are semantic counterparts of predicates and are used to store [`Fact`]s in models.
///
/// **Note**: `Rel` is the counterpart of [`Pred`] at a semantic level.
///
/// [`Fact`]: Observation::Fact
/// [`Pred`]: razor_fol::syntax::Pred
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Rel(String);

impl Rel {
    /// Applies `self` to a list of witness terms.
    pub fn app<T: WitnessTerm>(self, terms: Vec<T>) -> Observation<T> {
        Observation::Fact {
            relation: self,
            terms,
        }
    }

    /// Applies the (nullary) `self`.
    pub fn app0<T: WitnessTerm>(self) -> Observation<T> {
        Observation::Fact {
            relation: self,
            terms: vec![],
        }
    }

    /// Applies the (unary) `self` on a witness term.
    pub fn app1<T: WitnessTerm>(self, first: T) -> Observation<T> {
        Observation::Fact {
            relation: self,
            terms: vec![first],
        }
    }

    /// Applies the (binary) `self` on two witness terms.
    pub fn app2<T: WitnessTerm>(self, first: T, second: T) -> Observation<T> {
        Observation::Fact {
            relation: self,
            terms: vec![first, second],
        }
    }

    /// Applies the (ternary) `self` on three witness terms.
    pub fn app3<T: WitnessTerm>(self, first: T, second: T, third: T) -> Observation<T> {
        Observation::Fact {
            relation: self,
            terms: vec![first, second, third],
        }
    }

    /// Applies the (4-ary) `self` on four witness terms.
    pub fn app4<T: WitnessTerm>(self, first: T, second: T, third: T, fourth: T) -> Observation<T> {
        Observation::Fact {
            relation: self,
            terms: vec![first, second, third, fourth],
        }
    }

    /// Applies the (5-ary) `self` on five witness terms.
    pub fn app5<T: WitnessTerm>(
        self,
        first: T,
        second: T,
        third: T,
        fourth: T,
        fifth: T,
    ) -> Observation<T> {
        Observation::Fact {
            relation: self,
            terms: vec![first, second, third, fourth, fifth],
        }
    }
}

impl<S: Into<String>> From<S> for Rel {
    fn from(s: S) -> Self {
        Rel(s.into())
    }
}

impl fmt::Display for Rel {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Rel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Represents positive units of information by which [`Model`][Model]s are
/// constructed. Once a `Model` is augmented by an observation, the observation remains
/// true in the model.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Observation<T: WitnessTerm> {
    /// Is a relational fact, indicating that an atomic formula is true about a list of model
    /// elements, denoted by a list of [witness terms][WitnessTerm].
    Fact { relation: Rel, terms: Vec<T> },

    /// Is an equational fact, corresponding to an identity between two model elements,
    /// denoted by a two [witness terms][WitnessTerm].
    Identity { left: T, right: T },
}

impl<T: WitnessTerm> fmt::Display for Observation<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Observation::Fact { relation, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "<{}({})>", relation, ts.join(", "))
            }
            Observation::Identity { left, right } => write!(f, "<{} = {}>", left, right),
        }
    }
}

impl<T: WitnessTerm> fmt::Debug for Observation<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Is the trait for various implementations of first-order models that are constructed by
/// the chase.
pub trait Model: Clone {
    /// Is the type of witness terms, denoting elements of this model.
    /// [`ElementType`](`WitnessTerm::ElementType`)
    /// is the type of elements for this model.
    type TermType: WitnessTerm;

    /// Returns a unique ID for `self`.
    fn get_id(&self) -> u64;

    /// Returns the domain of `self`. The domain of a model consists of all elements in the
    /// model.
    fn domain(&self) -> Vec<<Self::TermType as WitnessTerm>::ElementType>;

    /// Returns the set of relational [`Fact`]s that are true in `self`.
    ///
    /// [`Fact`]: Observation::Fact
    fn facts(&self) -> Vec<Observation<Self::TermType>>;

    /// Returns a set of all witness terms in `self` that are denoted by `element`.
    fn witness(
        &self,
        element: &<Self::TermType as WitnessTerm>::ElementType,
    ) -> Vec<Self::TermType>;

    /// Returns the element in `self` that is denoted by `witness`.
    fn element(
        &self,
        witness: &Self::TermType,
    ) -> Option<<Self::TermType as WitnessTerm>::ElementType>;

    /// Is called when the chase is returning a model, asking the model to do any postprocessing
    /// needed.
    fn finalize(self) -> Self;
}

/// Is the trait for types that represents a geometric sequent in the context of an
/// [implementation of the chase][bg].
///
/// [bg]: self#background
pub trait Sequent: Clone {
    /// Returns the *body* (premise) of the sequent as a formula.
    fn body(&self) -> FOF;

    /// Returns the *head* (consequence) of the sequent as a formula.
    fn head(&self) -> FOF;
}

impl<S: Sequent> Sequent for &S {
    fn body(&self) -> FOF {
        (*self).body()
    }

    fn head(&self) -> FOF {
        (*self).head()
    }
}

/// Is the trait of objects that convert an initial theory to sequents and provide the initial
/// (empty) model for a particular implementation.
pub trait PreProcessor {
    /// Is the type of [sequents][Sequent] created by this preprocessor.
    type Sequent;

    /// Is the type of the initial [model][Model], created by this preprocessor.
    type Model;

    /// Given a theory, returns an iterator of [sequents][Sequent] and an initial
    /// [model][Model] by applying the necessary pre-processing.
    fn pre_process(&self, theory: &Theory<FOF>) -> (Vec<Self::Sequent>, Self::Model);
}

/// Strategy is the trait of algorithms for choosing sequents in the context of an
/// implementation of the chase. Strategy instances provide the next sequent to be
/// evaluated by the chase.
///
/// **Note**: See [here](self#implementation) for more information about how strategy instances are used.
pub trait Strategy<S: Sequent>: Clone + Iterator<Item = S> + FromIterator<S> {}

impl<S, Stg> Strategy<S> for Stg
where
    S: Sequent,
    Stg: Clone + Iterator<Item = S> + FromIterator<S>,
{
}

/// Bounder is the trait of algorithms for [bounding] the size of models generated by the chase.
///
/// [bounding]: self#termination
pub trait Bounder {
    /// Returns true if the given observation is outside of the bounds set for the given model
    /// according to the algorithm implemented by `self`. If the result is true, the chase
    /// stops processing the model.
    fn bound<M: Model>(&self, model: &M, observation: &Observation<M::TermType>) -> bool;
}

/// Is the trait of algorithms that evaluate an implementation of [Sequent] in an
/// implementation of [Model] within a [chase-step].
///
/// [chase-step]: self#chase-step
pub trait Evaluator<'s, Stg: Strategy<&'s Self::Sequent>, B: Bounder> {
    /// The type of [sequents][Sequent] that are accepted by this evaluator.
    type Sequent: Sequent + 's;

    /// The type of [models][Model] that can be processed by this evaluator.
    type Model: Model;

    /// Applies a [chase-step] by evaluating the sequents of `strategy` in `model` and produces
    /// extensions of `model`, corresponding to new branches of the chase. New models that do not
    /// reach the bound provided by `bounder` are returned as `open_models` in the resulting
    /// [`EvaluateResult`]. New models that reach the bound provided by `bounder` are returned
    /// as `bounded_models` in the return value.
    ///
    /// **Note**: The `open_models` in the return value will be scheduled for future chase-steps.
    ///
    /// [chase-step]: self#chase-step
    fn evaluate(
        &self,
        model: &Self::Model,
        strategy: &mut Stg,
        bounder: Option<&B>,
    ) -> Option<EvaluateResult<Self::Model>>;
}

/// Is result of [evaluating][Evaluator] a model in a [chase-step].
///
/// [chase-step]: self#chase-step
pub struct EvaluateResult<M: Model> {
    /// Is a list of all not-bounded extensions of a model after [evaluation].
    ///
    /// [evaluation]: Evaluator::evaluate()
    open_models: Vec<M>,

    /// Is a list of bounded extensions of a model after a [evaluation].
    ///
    /// [evaluation]: Evaluator::evaluate()
    bounded_models: Vec<M>,
}

impl<M: Model> EvaluateResult<M> {
    /// Returns an empty instance of [`EvaluateResult`].
    pub fn new() -> Self {
        Self {
            open_models: Vec::new(),
            bounded_models: Vec::new(),
        }
    }

    /// Returns true if `self` contains no models (neither `open_models` nor `bounded_models`)
    /// and false otherwise.
    pub fn empty(&self) -> bool {
        self.open_models.is_empty() && self.bounded_models.is_empty()
    }

    /// Appends `model` to the list of `open_models` of `self`.
    pub fn append_open_model(&mut self, model: M) {
        self.open_models.push(model);
    }

    /// Appends `model` to the list of `bounded_models` of `self`.
    pub fn append_bounded_model(&mut self, model: M) {
        self.bounded_models.push(model);
    }

    /// Appends the value in `model` to the list of `open_models` or `bounded_models` of
    /// `self` if `model` is respectively a left or a right value.
    pub fn append(&mut self, model: Either<M, M>) {
        match model {
            Either::Left(m) => self.append_open_model(m),
            Either::Right(m) => self.append_bounded_model(m),
        };
    }

    /// Consumes `self` and returns a tuple of its open and bounded models.
    pub fn into_models(self) -> (Vec<M>, Vec<M>) {
        (self.open_models, self.bounded_models)
    }
}

impl<M: Model> Default for EvaluateResult<M> {
    fn default() -> Self {
        Self::new()
    }
}

impl<M: Model> From<Vec<Either<M, M>>> for EvaluateResult<M> {
    fn from(models: Vec<Either<M, M>>) -> Self {
        let mut result = EvaluateResult::new();
        models.into_iter().for_each(|m| result.append(m));
        result
    }
}

impl<M: Model> From<(Vec<M>, Vec<M>)> for EvaluateResult<M> {
    fn from(models: (Vec<M>, Vec<M>)) -> Self {
        let mut result = EvaluateResult::new();
        result.open_models = models.0;
        result.bounded_models = models.1;
        result
    }
}

/// Is the trait of algorithms for scheduling various branches of the chase. A branch of the chase
/// is represented with a [model][Model] together with a [strategy][Strategy] for
/// scheduling sequents to be evaluated in the model.
///
/// **Note**: See [here] for more information about scheduling branches of the chase.
///
/// [here]: self#implementation
pub trait Scheduler<S: Sequent, M: Model, Stg: Strategy<S>> {
    /// Returns true if the scheduler is empty and false otherwise.
    fn empty(&self) -> bool;

    /// Schedules a [model][Model] and its associated [strategy][Strategy] as a
    /// branch of the chase.
    fn add(&mut self, model: M, strategy: Stg);

    /// Removes the next scheduled item from `self` and returns its associated
    /// [model][Model] and [strategy][Strategy].
    fn remove(&mut self) -> Option<(M, Stg)>;
}

/// Given a [`scheduler`][Scheduler], an [`evaluator`][Evaluator] and possibly a
/// [`bounder`][Bounder], runs an implementation independent run of [the chase] and
/// returns *all* resulting models. The return value is empty if the theory is not satisfiable.
///
/// [the chase]: self#the-chase
///
/// ```rust
/// use razor_fol::syntax::{FOF, Theory};
/// use razor_chase::chase::{
///     PreProcessor, Scheduler, Strategy, chase_all,
///     r#impl::basic,
///     strategy::Linear,
///     scheduler::FIFO,
///     bounder::DomainSize,
/// };
///
/// // parse the theory:
/// let theory: Theory<FOF> = r#"
///   exists x . P(x);
///   P(x) implies Q(x) | R(x);
///   R(x) -> exists y . S(x, y);
/// "#.parse().unwrap();
///
/// // preprocess the theory to get geometric sequents and an initial (empty) model:
/// let pre_processor = basic::BasicPreProcessor;
/// let (sequents, init_model) = pre_processor.pre_process(&theory);
///
/// let evaluator = basic::BasicEvaluator {};
/// let strategy: Linear<_> = sequents.iter().collect(); // use the `Linear` strategy
/// let mut scheduler = FIFO::new();  // schedule branches in first-in-first-out manner
///
/// // run unbounded model-finding (note that the chase terminates on the given theory):
/// let bounder: Option<&DomainSize> = None;
/// scheduler.add(init_model, strategy); // schedule the initial (empty) model
/// let models = chase_all(&mut scheduler, &evaluator, bounder);
///
/// assert_eq!(2, models.len()); // two models are found
/// ```
pub fn chase_all<'s, S, M, Stg, Sch, E, B>(
    scheduler: &mut Sch,
    evaluator: &E,
    bounder: Option<&B>,
) -> Vec<M>
where
    S: 's + Sequent,
    M: Model + std::fmt::Debug,
    Stg: Strategy<&'s S>,
    Sch: Scheduler<&'s S, M, Stg>,
    E: Evaluator<'s, Stg, B, Sequent = S, Model = M>,
    B: Bounder,
{
    let mut complete = Vec::new();
    let mut incomplete = Vec::new();
    while !scheduler.empty() {
        chase_step(
            scheduler,
            evaluator,
            bounder,
            |m| complete.push(m.finalize()),
            |m| incomplete.push(m.finalize()),
        );
    }
    complete.extend(incomplete);
    complete
}

/// Given a [`scheduler`][Scheduler], an [`evaluator`][Evaluator], possibly a
/// [`bounder`][Bounder] and a `consumer` closure, runs an implementation independent
/// [chase-step]. Satisfying models of the theory that are produced
/// by the `chase-step` will be consumed by the `consumer`. In contrast, `incomplete_consumer`
/// (if provided) consumes incomplete non-models of the theory that are rejected by the
/// bounder.
///
/// [chase-step]: self#chase-step
///
/// ```rust
/// use razor_fol::syntax::{FOF, Theory};
/// use razor_chase::chase::{
///     PreProcessor, Scheduler, Strategy, chase_step,
///     r#impl::basic,
///     strategy::Linear,
///     scheduler::FIFO,
///     bounder::DomainSize,
/// };
/// use std::convert::TryInto;
///
/// // parse the theory:
/// let theory: Theory<FOF> = r#"
///   exists x . P(x);
///   P(x) implies Q(x) | R(x);
///   R(x) -> exists y . S(x, y);
/// "#.parse().unwrap();
///
/// // preprocess the theory to get geometric sequents and an initial (empty) model:
/// let pre_processor = basic::BasicPreProcessor;
/// let (sequents, init_model) = pre_processor.pre_process(&theory);
///
/// let evaluator = basic::BasicEvaluator {};
/// let strategy: Linear<_> = sequents.iter().collect(); // use the `Linear` strategy
/// let mut scheduler = FIFO::new();  // schedule branches in first-in-first-out manner
///
/// // run unbounded model-finding (note that the chase terminates on the given theory):
/// let bounder: Option<&DomainSize> = None;
/// scheduler.add(init_model, strategy); // schedule the initial (empty) model
///
/// let mut counter = 0;       // a counter to count the number of models
/// while !scheduler.empty() {
///     let models = chase_step(
///         &mut scheduler,
///         &evaluator,
///         bounder,
///         |m| {counter += 1}, // the closure counts the models found
///         |_|{},               // ignore incomplete non-models
///     );
/// }
///
/// assert_eq!(2, counter); // two models are found
/// ```
pub fn chase_step<'s, S, M, Stg, Sch, E, B>(
    scheduler: &mut Sch,
    evaluator: &E,
    bounder: Option<&B>,
    mut consumer: impl FnMut(M),
    mut incomplete_consumer: impl FnMut(M),
) where
    S: 's + Sequent,
    M: Model + std::fmt::Debug,
    Stg: Strategy<&'s S>,
    Sch: Scheduler<&'s S, M, Stg>,
    E: Evaluator<'s, Stg, B, Sequent = S, Model = M>,
    B: Bounder,
{
    let (base_model, mut strategy) = scheduler.remove().unwrap();
    let base_id = &base_model.get_id();
    let span = span!(
        tracing::Level::TRACE,
        super::trace::CHASE_STEP,
        id = base_id
    );
    let result = evaluator.evaluate(&base_model, &mut strategy, bounder);

    if let Some(result) = result {
        if !result.empty() {
            let (open, bounded) = result.into_models();
            open.into_iter().for_each(|m| {
                let _enter = span.enter();
                info!(
                    event = super::trace::EXTEND,
                    model_id = &m.get_id(),
                    parent = base_id,
                    model = ?m,
                );
                scheduler.add(m, strategy.clone());
            });
            bounded.into_iter().for_each(|m| {
                let _enter = span.enter();
                info!(
                    event = super::trace::BOUND,
                    model_id = &m.get_id(),
                    parent = base_id,
                    model = ?m,
                );
                incomplete_consumer(m);
            });
        } else {
            let _enter = span.enter();
            info!(
                event = super::trace::MODEL,
                model_id = &base_id,
                model = ?base_model,
            );
            consumer(base_model);
        }
    } else {
        let _enter = span.enter();
        info!(
            event = super::trace::FAIL,
            model_id = &base_id,
            model = ?base_model,
        );
    }
}

//// Tests -------------------------------------
#[cfg(test)]
mod test_chase {
    use crate::test_prelude::*;

    #[test]
    fn test_element() {
        assert_eq!("e#0", e_0().to_string());
        assert_eq!(e_0(), e_0());
        assert_ne!(e_0(), e_1());
        assert!(e_0() < e_1());
        assert!(!(e_0() > e_1()));
        assert!(!(e_1() > e_1()));
        assert!(!(e_1() < e_1()));
        {
            let mut e0 = e_0();
            let e1 = e_1();
            e0.identify(&e1);
            assert_eq!(e_1(), e0);
            assert_eq!(e_1(), e1);
        }
    }

    #[test]
    fn test_rel() {
        assert_eq!(_R_(), R().name().into());
        assert_eq!("R", _R_().to_string());
    }
}
