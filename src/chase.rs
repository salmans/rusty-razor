//! Provides a framework and interfaces to various components that are used for implementing the
//! Chase. It also implements entrypoints for running the Chase.
//!
//! ## Background
//! Razor uses a variant of [the Chase] algorithm to construct models for first-order theories with
//! equality. The Chase operates on *[geometric theories]*, theories that contain a syntactic
//! variation of first-order formulae which we refer to as the Geometric Normal Form (GNF). Formulae
//! in GNF have the following general shape:
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
//! where A<sub>k</sub>s are (positive) atomic formulae (possibly including equations) and free
//! variables are assumed to be universally qualified over the entire formula.
//!
//! In the context of a [run of the Chase], we refer to any formula in the geometric theory as a
//! *[sequent]*. The premise (left side) and the consequence (right side) of the implication are
//! respectively said to be the *body* and the *head* of the sequent.
//!
//! ### Satisfiability of Geometric Theories
//! It turns out that every first-order theory can be transformed to a geometric theory that is
//! *equisatisfiable* to the original theory via [standard syntactic manipulation].
//! In fact, for every model *N* of the original theory, there exists a model *M* of the geometric
//! theory such that there is a homomorphism from *M* to *N*. This is an important result that
//! enables Razor to utilize the Chase to construct homomorphically minimal models of a given
//! first-order theory.
//!
//! In the context of a model-finding application, the models that the Chase produces are desirable
//! since they contain minimum amount of information, thus they induce minimal distraction.
//! As a direct consequence of semi-decidability of satisfiability in first-order logic
//! (see [Gödel's incompleteness theorems][godel]), satisfiability of geometric theories is too
//! semi-decidable.
//!
//! **Note**: A comprehensive discussion on the properties of the models that are constructed by
//! the Chase is out of the scope of this document.
//!
//! [the Chase]: https://en.wikipedia.org/wiki/Chase_(algorithm)
//! [PhD dissertation]: https://digitalcommons.wpi.edu/etd-dissertations/458/
//! [geometric theories]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
//! [run of the Chase]: ./fn.solve_all.html
//! [sequent]: ./trait.SequentTrait.html
//! [standard syntactic manipulation]: ../formula/syntax/enum.Formula.html#method.gnf
//! [godel]: https://en.wikipedia.org/wiki/Gödel%27s_incompleteness_theorems
//!
//! ## The Chase
//! Given a geometric theory and starting with an empty model, a run of Chase consists of repeated
//! applications of [chase-step]s by which the model is augmented with *necessary* pieces of
//! information until there is a contraction or the model satisfies the theory. Within
//! Razor's implementation, instances of any type that implements [ModelTrait] can serve as a
//! first-order model. Also, inspired by [Steven Vickers][vickers], we refer to the units of
//! information that augment models as [observation]s.
//!
//! [chase-step]: index.html#chase-step
//! [vickers]: https://www.cs.bham.ac.uk/~sjv/GeoZ.pdf
//!
//! ### Chase Step
//! Given a geometric theory and an existing model, a chase-step proceeds as follows:
//!
//! 1. A sequent from the theory is selected to be evaluated against the model. Razor uses an
//! instance of [StrategyTrait] to select the sequent.
//!
//! 2. The selected sequent is evaluated against the model: given an assignment from the free
//! variables of the sequent to the elements of the model, if the body of the sequent is true and
//! its head is not true in the model, new observations are added to the model to make the
//! sequent's head true. Instances of any type that implements [EvaluatorTrait] may be used to
//! evaluate the sequent in the model.
//!
//!     2.1. If the sequent is headless, meaning its consequence is falsehood (an empty disjunction),
//! the Chase fails on the given model.
//!
//!     2.2. If the head of the sequent contains more than one disjunct (with at least one
//! non-trivial disjunction), the Chase branches and satisfies each disjunct independently on clones
//! of the model. Razor uses instances of [SchedulerTrait] to schedule various branches of the Chase
//! for future Chase steps.
//!
//!     2.3. If no sequent can be found such that its body and head are respectively true and false
//! in the model, the model already satisfies the theory and will be returned as an output of the
//! Chase.
//!
//! [model]: ./trait.ModelTrait.html
//! [observation]: ./enum.Observation.html
//! [ModelTrait]: ./trait.ModelTrait.html
//! [StrategyTrait]: ./trait.StrategyTrait.html
//! [EvaluatorTrait]: ./trait.EvaluatorTrait.html
//! [SchedulerTrait]: ./trait.SchedulerTrait.html
//!
//! ### Termination
//! As a result of semi-decidability of geometric theories, it can be shown if a geometric theory
//! is unsatisfiable, a run of the Chase on the theory always terminates, although it may take
//! a very very long time.
//! However, when the theory is satisfiable, a run of the Chase may not terminate, producing
//! infinitely large models and/or infinitely many models that satisfy the theory. Nevertheless,
//! for a practical application such as for Razor, we can *bound* the size of models created by the
//! Chase to guarantee termination. Razor uses instances of types that implement [BounderTrait] to
//! implement various strategies to cap the size of search space for models.
//!
//! [BounderTrait]: ./trait.BounderTrait.html
//!
//! ## Implementation
//! The primary motivation for implementing Razor is to study the Chase and improve its performance
//! for practical applications. The flexible (but somehow complex) design of Razor allows for
//! experimenting with various data structures to represent [models] and [sequents], [evaluating]
//! sequents in models using a variety of algorithms, testing different ideas for [scheduling]
//! branches of the Chase and devising various [strategies] for selecting sequents. Also, because of
//! theoretical and non-theoretical consequences of non-termination of the Chase, Razor is going to
//! explore a variety of ideas for limiting the search space by [bounding] the size of models:
//!
//! Interesting combinations of these various options are constantly benchmarked and the
//! configuration with the best average performance is used by the Rusty Razor application.
//!
//! [models]: ./trait.ModelTrait.html
//! [sequents]: ./trait.SequentTrait.html
//! [evaluating]: ./trait.EvaluatorTrait.html
//! [scheduling]: ./trait.SchedulerTrait.html
//! [strategies]: ./trait.StrategyTrait.html
//! [bounding]: ./trait.BounderTrait.html
//!
pub mod r#impl;
pub mod strategy;
pub mod scheduler;
pub mod bounder;

use crate::formula::syntax::*;
use std::fmt;

use tracing;
use itertools::Either;

/// Is a symbol to represent elements of first-order models. An element is identified by an index.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct E(pub i32);

impl E {
    /// Identifies the receiver with `other` element by collapsing their indices.
    /// ```rust
    /// # use rusty_razor::chase::E;
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
pub trait WitnessTermTrait: Clone + PartialEq + Eq + fmt::Display + FApp {
    /// Is the type of elements that are witnessed by the witness term.
    ///
    /// **Note**: Although [`E`] is often the underlying symbol for representing model
    /// elements, models may implement their own element types based on or independent from `E`.
    /// See [`chase::impl::reference::Model`](./impl/reference/struct.Model.html) for an example.
    ///
    /// [`E`]: ./struct.E.html
    ///
    type ElementType;

    /// Returns an equational [`Observation`] between the receiver and the given [witness term].
    ///
    /// [`Observation`]: ./enum.Observation.html
    /// [witness term]: ./trait.WitnessTermTrait.html
    fn equals(self, rhs: Self) -> Observation<Self> {
        Observation::Identity { left: self, right: rhs }
    }
}

/// Relations are semantic counterparts of predicates and are used to store [`Fact`]s in models.
///
/// **Note**: `Rel` is the counterpart of [`Pred`] at a semantic level.
///
/// [`Fact`]: ./enum.Observation.html#variant.Fact
/// [`Pred`]: ../formula/syntax/struct.Pred.html
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Rel(pub String);

impl Rel {
    /// Applies the receiver to a list of witness terms.
    pub fn app<T: WitnessTermTrait>(self, terms: Vec<T>) -> Observation<T> {
        Observation::Fact { relation: self, terms }
    }

    /// Applies the (nullary) receiver.
    pub fn app0<T: WitnessTermTrait>(self) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![] }
    }

    /// Applies the (unary) receiver on a witness term.
    pub fn app1<T: WitnessTermTrait>(self, first: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first] }
    }

    /// Applies the (binary) receiver on two witness terms.
    pub fn app2<T: WitnessTermTrait>(self, first: T, second: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second] }
    }

    /// Applies the (ternary) receiver on three witness terms.
    pub fn app3<T: WitnessTermTrait>(self, first: T, second: T, third: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second, third] }
    }

    /// Applies the (4-ary) receiver on four witness terms.
    pub fn app4<T: WitnessTermTrait>(self, first: T, second: T, third: T, fourth: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second, third, fourth] }
    }

    /// Applies the (5-ary) receiver on five witness terms.
    pub fn app5<T: WitnessTermTrait>(self, first: T, second: T, third: T, fourth: T, fifth: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second, third, fourth, fifth] }
    }
}

impl From<&str> for Rel {
    fn from(s: &str) -> Self {
        Rel(s.to_owned())
    }
}

impl From<String> for Rel {
    fn from(s: String) -> Self {
        Rel(s)
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

impl From<Pred> for Rel {
    fn from(predicate: Pred) -> Self {
        Rel(predicate.0)
    }
}

/// Represents positive units of information by which [`Model`]s are constructed. Once a `Model` is
/// augmented by an observation, the observation remains true in the model.
///
/// [`Model`]: ./trait.ModelTrait.html
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Observation<T: WitnessTermTrait> {
    /// Is a relational fact, indicating that an atomic formula is true about a list of model
    /// elements, denoted by a list of [witness terms].
    ///
    /// [witness terms]: ./trait.WitnessTermTrait.html
    Fact { relation: Rel, terms: Vec<T> },

    /// Is an equational fact, corresponding to an identity between two model elements, denoted
    /// by a two [witness terms].
    ///
    /// [witness terms]: ./trait.WitnessTermTrait.html
    Identity { left: T, right: T },
}

impl<T: WitnessTermTrait> fmt::Display for Observation<T> {
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

impl<T: WitnessTermTrait> fmt::Debug for Observation<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

/// Is the trait for various implementations of first-order models that are constructed by the
/// Chase.
pub trait ModelTrait: Clone + fmt::Display + ToString {
    /// Is the type of witness terms, denoting elements of this model. [`WitnessTerm::ElementType`]
    /// is the type of elements for this model.
    ///
    /// [`WitnessTerm::ElementType`]: ./trait.WitnessTermTrait.html#associatedtype.ElementType
    type TermType: WitnessTermTrait;

    /// Returns a unique ID for the receiver.
    fn get_id(&self) -> u64;

    /// Returns the domain of the receiver. The domain of a model consists of all elements in the
    /// model.
    fn domain(&self) -> Vec<&<Self::TermType as WitnessTermTrait>::ElementType>;

    /// Returns the set of relational [`Fact`]s that are true in the receiver.
    ///
    /// [`Fact`]: ./enum.Observation.html#variant.Fact
    fn facts(&self) -> Vec<&Observation<Self::TermType>>;

    /// Augments the receiver with `observation`, making `observation`true in the receiver.
    fn observe(&mut self, observation: &Observation<Self::TermType>);

    /// Returns true if `observation` is true in the receiver; otherwise, returns false.
    fn is_observed(&self, observation: &Observation<Self::TermType>) -> bool;

    /// Returns a set of all witness terms in the receiver that are denoted by `element`.
    fn witness(&self, element: &<Self::TermType as WitnessTermTrait>::ElementType) -> Vec<&Self::TermType>;

    /// Returns the element in the receiver that is denoted by `witness`.
    fn element(&self, witness: &Self::TermType) -> Option<&<Self::TermType as WitnessTermTrait>::ElementType>;
}

/// Is the trait for types that represents a [geometric sequent][sequent] in the
/// context of an implementation of the Chase.
///
/// [sequent]: ./index.html#background
pub trait SequentTrait: Clone {
    /// Returns the *body* (premise) of the sequent as a [formula].
    ///
    /// [formula]: ../formula/syntax/enum.Formula.html
    fn body(&self) -> Formula;

    /// Returns the *head* (consequence) of the sequent as a [formula].
    ///
    /// [formula]: ../formula/syntax/enum.Formula.html
    fn head(&self) -> Formula;
}

/// Strategy is the trait of algorithms for choosing sequents in the context of an implementation
/// of the Chase. Strategy instances provide the next sequent to be evaluated by the Chase.
///
/// **Note**: See [here] for more information about how strategy instances are used.
///
/// [here]: ./index.html#implementation
pub trait StrategyTrait: Clone + Iterator {
    /// Construct an instance of `Strategy` from a given list of sequents as items.
    fn new(sequents: Vec<Self::Item>) -> Self;
}

/// Bounder is the trait of algorithms for [bounding] the size of models generated by the Chase.
///
/// [bounding]: ./index.html#termination
pub trait BounderTrait {
    /// Returns true if the given observation is outside of the bounds set for the given model
    /// according to the algorithm implemented by the receiver. If the result is true, the Chase
    /// stops processing the model.
    fn bound<M: ModelTrait>(&self, model: &M, observation: &Observation<M::TermType>) -> bool;
}

/// Is the trait of algorithms that evaluate an implementation of [SequentTrait] in an
/// implementation of [ModelTrait] within a [chase-step].
///
/// [SequentTrait]: ./trait.SequentTrait.html
/// [ModelTrait]: ./trait.ModelTrait.html
/// [chase-step]: ./index.html#chase-step
pub trait EvaluatorTrait<'s, Stg: StrategyTrait<Item=&'s Self::Sequent>, B: BounderTrait> {
    /// The type of [sequents] that can be processed by this evaluator.
    ///
    /// [SequentTrait]: ./trait.SequentTrait.html
    type Sequent: 's + SequentTrait;

    /// The type of [models] that can be processed by this evaluator.
    ///
    /// [models]: ./trait.ModelTrait.html
    type Model: ModelTrait;

    /// Applies a [chase-step] by evaluating the sequents of `strategy` in `model` and produces
    /// extensions of `model`, corresponding to new branches of the Chase. New models that do not
    /// reach the bound provided by `bounder` are returned as `open_models` in the resulting
    /// [`EvaluateResult`]. New models that reach the bound provided by `bounder` are returned
    /// as `bounded_models` in the return value.
    ///
    /// **Note**: The `open_models` in the return value will be scheduled for future chase-steps.
    ///
    /// [chase-step]: ./index.html#chase-step
    /// [`EvaluateResult`]: ./struct.EvaluateResult.html
    fn evaluate(
        &self,
        model: &Self::Model,
        strategy: &mut Stg,
        bounder: Option<&B>,
    ) -> Option<EvaluateResult<Self::Model>>;
}

/// Is result of [evaluating] a model in a [chase-step].
///
/// [evaluating]: ./trait.EvaluatorTrait.html
/// [chase-step]: ./index.html#chase-step
pub struct EvaluateResult<M: ModelTrait> {
    /// Is a list of all not-bounded extensions of a model after [evaluation].
    ///
    /// [evaluation]: ./trait.EvaluatorTrait.html#tymethod.evaluate
    open_models: Vec<M>,

    /// Is a list of bounded extensions of a model after a [evaluation].
    ///
    /// [evaluation]: ./trait.EvaluatorTrait.html#tymethod.evaluate
    bounded_models: Vec<M>,
}

impl<M: ModelTrait> EvaluateResult<M> {
    /// Returns an empty instance of [`EvaluateResult`].
    ///
    /// [`EvaluateResult`]: ./struct.EvaluateResult.html
    pub fn new() -> Self {
        Self {
            open_models: Vec::new(),
            bounded_models: Vec::new(),
        }
    }

    /// Returns true if the receiver contains no models (neither `open_models` nor `bounded_models`)
    /// and false otherwise.
    pub fn empty(&self) -> bool {
        self.open_models.is_empty() && self.bounded_models.is_empty()
    }

    /// Clears the list of `open_models` in the receiver.
    pub fn clear_open_models(&mut self) {
        self.open_models.clear();
    }

    /// Clears the list of `bounded_models` in the receiver.
    pub fn clear_bounded_models(&mut self) {
        self.bounded_models.clear();
    }

    /// Appends `model` to the list of `open_models` of the receiver.
    pub fn append_open_model(&mut self, model: M) {
        self.open_models.push(model);
    }

    /// Appends `model` to the list of `bounded_models` of the receiver.
    pub fn append_bounded_model(&mut self, model: M) {
        self.bounded_models.push(model);
    }

    /// Appends the value in `model` to the list of `open_models` or `bounded_models` of the
    /// receiver if `model` is respectively a left or a right value.
    pub fn append(&mut self, model: Either<M, M>) {
        match model {
            Either::Left(m) => self.append_open_model(m),
            Either::Right(m) => self.append_bounded_model(m),
        };
    }
}

impl<M: ModelTrait> From<Vec<Either<M, M>>> for EvaluateResult<M> {
    fn from(models: Vec<Either<M, M>>) -> Self {
        let mut result = EvaluateResult::new();
        models.into_iter().for_each(|m| result.append(m));
        result
    }
}

/// Is the trait of algorithms for scheduling various branches of the Chase. A branch of the Chase
/// is represented with a [model] together with a [strategy] for scheduling sequents to be
/// evaluated in the model.
///
/// **Note**: See [here] for more information about scheduling branches of the Chase.
///
/// [model]: ./trait.ModelTrait.html
/// [strategy]: ./trait.StrategyTrait.html
/// [here]: ./index.html#implementation
pub trait SchedulerTrait<'s, S: 's + SequentTrait, M: ModelTrait, Stg: StrategyTrait<Item=&'s S>> {
    /// Returns true if the scheduler is empty and false otherwise.
    fn empty(&self) -> bool;

    /// Schedules a [model] and its associated [strategy] as a branch of the Chase.
    ///
    /// [model]: ./trait.ModelTrait.html
    /// [strategy]: ./trait.StrategyTrait.html
    fn add(&mut self, model: M, strategy: Stg);

    /// Removes the next scheduled item from the receiver and returns its associated [model] and
    /// [strategy].
    ///
    /// [model]: ./trait.ModelTrait.html
    /// [strategy]: ./trait.StrategyTrait.html
    fn remove(&mut self) -> Option<(M, Stg)>;
}

/// Given a [`scheduler`], an [`evaluator`] and possibly a [`bounder`], runs an implementation
/// independent run of [the Chase] and returns *all* resulting models. The return value is empty if
/// the theory is not satisfiable.
///
/// [`scheduler`]: ./trait.SchedulerTrait.html
/// [`evaluator`]: ./trait.EvaluatorTrait.html
/// [`bounder`]: ./trait.BounderTrait.html
/// [the Chase]: ./index.html#the-chase
///
/// ```rust
/// use rusty_razor::formula::syntax::Theory;
/// use rusty_razor::chase::{
///     SchedulerTrait, StrategyTrait, chase_all,
///     r#impl::basic,
///     strategy::Linear,
///     scheduler::FIFO,
///     bounder::DomainSize,
/// };
///
/// // parse the theory:
/// let theory: Theory = r#"
///   exists x . P(x);
///   P(x) implies Q(x) | R(x);
///   R(x) -> exists y . Q(x, y);
/// "#.parse().unwrap();
///
/// let geometric_theory = theory.gnf(); // convert the theory to geometric
///
/// // create sequents for the geometric theory:
/// let sequents: Vec<basic::Sequent> = geometric_theory
///     .formulae
///     .iter()
///     .map(|f| f.into())
///     .collect();
///
/// let evaluator = basic::Evaluator {};
/// let strategy = Linear::new(sequents.iter().collect()); // use the `Linear` strategy
/// let mut scheduler = FIFO::new();  // schedule branches in first-in-first-out manner
///
/// // run unbounded model-finding (note that the Chase terminates on the given theory):
/// let bounder: Option<&DomainSize> = None;
/// scheduler.add(basic::Model::new(), strategy); // schedule the initial (empty) model
/// let models = chase_all(&mut scheduler, &evaluator, bounder);
///
/// assert_eq!(2, models.len()); // two models are found
/// ```
pub fn chase_all<'s, S, M, Stg, Sch, E, B>(
    scheduler: &mut Sch,
    evaluator: &E,
    bounder: Option<&B>,
) -> Vec<M>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Stg: StrategyTrait<Item=&'s S>,
          Sch: SchedulerTrait<'s, S, M, Stg>,
          E: EvaluatorTrait<'s, Stg, B, Sequent=S, Model=M>,
          B: BounderTrait {
    let mut result: Vec<M> = Vec::new();
    while !scheduler.empty() {
        chase_step(scheduler, evaluator, bounder, |m| result.push(m), |_|{});
    }
    result
}

/// Given a [`scheduler`], an [`evaluator`], possibly a [`bounder`] and a `consumer` closure, runs
/// an implementation independent [chase-step]. Satisfying models of the theory that are produced
/// by the `chase-step` will be consumed by the `consumer`. In contrast, `incomplete_consumer`
/// (if provided) consumes incomplete non-models of the theory that are rejected by the bounder.
///
/// [`scheduler`]: ./trait.SchedulerTrait.html
/// [`evaluator`]: ./trait.EvaluatorTrait.html
/// [`bounder`]: ./trait.BounderTrait.html
/// [chase-step]: ./index.html#chase-step
///
/// ```rust
/// use rusty_razor::formula::syntax::Theory;
/// use rusty_razor::chase::{
///     SchedulerTrait, StrategyTrait, chase_step,
///     r#impl::basic,
///     strategy::Linear,
///     scheduler::FIFO,
///     bounder::DomainSize,
/// };
///
/// // parse the theory:
/// let theory: Theory = r#"
///   exists x . P(x);
///   P(x) implies Q(x) | R(x);
///   R(x) -> exists y . Q(x, y);
/// "#.parse().unwrap();
///
/// let geometric_theory = theory.gnf(); // convert the theory to geometric
///
/// // create sequents for the geometric theory:
/// let sequents: Vec<basic::Sequent> = geometric_theory
///     .formulae
///     .iter()
///     .map(|f| f.into())
///     .collect();
///
/// let evaluator = basic::Evaluator {};
/// let strategy = Linear::new(sequents.iter().collect()); // use the `Linear` strategy
/// let mut scheduler = FIFO::new();  // schedule branches in first-in-first-out manner
///
/// // run unbounded model-finding (note that the Chase terminates on the given theory):
/// let bounder: Option<&DomainSize> = None;
/// scheduler.add(basic::Model::new(), strategy); // schedule the initial (empty) model
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
) where S: 's + SequentTrait,
        M: ModelTrait,
        Stg: StrategyTrait<Item=&'s S>,
        Sch: SchedulerTrait<'s, S, M, Stg>,
        E: EvaluatorTrait<'s, Stg, B, Sequent=S, Model=M>,
        B: BounderTrait {
    let (base_model, mut strategy) = scheduler.remove().unwrap();
    let base_id = &base_model.get_id();
    let span = span!(tracing::Level::TRACE, super::trace::CHASE_STEP, id = base_id);
    let models = evaluator.evaluate(&base_model, &mut strategy, bounder);

    if let Some(models) = models {
        if !models.empty() {
            models.open_models.into_iter().for_each(|m| {
                let _enter = span.enter();
                info!(
                        event = super::trace::EXTEND,
                        model_id = &m.get_id(),
                        parent = base_id,
                        model = %m,
                    );
                scheduler.add(m, strategy.clone());
            });
            models.bounded_models.into_iter().for_each(|m| {
                let _enter = span.enter();
                info!(
                        event = super::trace::BOUND,
                        model_id = &m.get_id(),
                        parent = base_id,
                        model = %m,
                    );
                incomplete_consumer(m);
            });
        } else {
            let _enter = span.enter();
            info!(
                event = super::trace::MODEL,
                model_id = &base_id,
                model = %base_model,
            );
            consumer(base_model);
        }
    } else {
        let _enter = span.enter();
        info!(
            event = super::trace::FAIL,
            model_id = &base_id,
            model = %base_model,
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
        assert_eq!(_R_(), R().into());
        assert_eq!("R", _R_().to_string());
    }
}
