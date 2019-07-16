pub mod r#impl;
pub mod selector;
pub mod strategy;
pub mod bounder;

use crate::formula::syntax::*;
use itertools::Either;
use std::fmt;

use tracing;

/// ## Element
/// Element symbols represent elements of models.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct E(pub i32);

impl E {
    pub fn new(name: i32) -> E {
        E(name)
    }

    /// Identifies the element with another elemen and is used for equality reasoning.
    pub fn identify(&mut self, other: &Self) {
        self.0 = other.0;
    }
}

impl fmt::Display for E {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "e#{}", self.0)
    }
}

/// ## Witness Term
/// Witness terms are variable free terms that provide provenance information to justify elements
/// of models.
pub trait WitnessTermTrait: Clone + PartialEq + Eq + fmt::Display + FuncApp {
    /// The internal representation of an element when implementing a WitnessTerm.
    type ElementType;

    /// Constructs an Identity observation for two witness terms.
    fn equals(self, rhs: Self) -> Observation<Self> {
        Observation::Identity { left: self, right: rhs }
    }
}

/// ## Relation
/// Relations are semantic counterparts of predicates and are used to construct observations.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Rel(pub String);

impl Rel {
    pub fn new(name: &str) -> Rel {
        Rel(name.to_owned())
    }
    /// Applies the relation to a list of witness terms.
    pub fn app<T: WitnessTermTrait>(self, terms: Vec<T>) -> Observation<T> {
        Observation::Fact { relation: self, terms }
    }
    /// Applies the relation to a list of terms.
    pub fn app0<T: WitnessTermTrait>(self) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![] }
    }
    /// Applies the (unary) relation to a witness term.
    pub fn app1<T: WitnessTermTrait>(self, first: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first] }
    }
    /// Applies the (binary) predicate to two witness terms.
    pub fn app2<T: WitnessTermTrait>(self, first: T, second: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second] }
    }
    /// Applies the (ternary) relation to three witness terms.
    pub fn app3<T: WitnessTermTrait>(self, first: T, second: T, third: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second, third] }
    }
    /// Applies the (4-ary) relation to four witness terms.
    pub fn app4<T: WitnessTermTrait>(self, first: T, second: T, third: T, fourth: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second, third, fourth] }
    }
    /// Applies the (5-ary) relation to five witness terms.
    pub fn app5<T: WitnessTermTrait>(self, first: T, second: T, third: T, fourth: T, fifth: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second, third, fourth, fifth] }
    }
}

impl fmt::Display for Rel {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl From<Pred> for Rel {
    fn from(predicate: Pred) -> Self {
        Rel(predicate.0)
    }
}

/// ## Observation
/// Observations are true positive *facts* that are true in the model.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Observation<T: WitnessTermTrait> {
    /// Relational fact
    Fact { relation: Rel, terms: Vec<T> },
    /// Identity fact
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

/// ## Model
/// Model is the common trait for various possible implementations of first order models, returned
/// by the chase.
pub trait ModelTrait: Clone + fmt::Display + ToString {
    type TermType: WitnessTermTrait;

    /// Returns a unique ID for the model (complete or partial) in its execution.
    fn get_id(&self) -> u64;
    /// Returns the domain of this model.
    fn domain(&self) -> Vec<&<Self::TermType as WitnessTermTrait>::ElementType>;
    /// Returns the set of observation facts that are true in this model.
    fn facts(&self) -> Vec<&Observation<Self::TermType>>;
    /// Makes the given observation hold in the model.
    fn observe(&mut self, observation: &Observation<Self::TermType>);
    /// Returns true if the given observation holds in the model.
    fn is_observed(&self, observation: &Observation<Self::TermType>) -> bool;
    /// Returns a set of all witness terms for the given element.
    fn witness(&self, element: &<Self::TermType as WitnessTermTrait>::ElementType) -> Vec<&Self::TermType>;
    /// Returns the element, associated with the given witness term.
    fn element(&self, witness: &Self::TermType) -> Option<&<Self::TermType as WitnessTermTrait>::ElementType>;
}

/// ## Sequent
/// Sequent is the common trait for various implementations of sequents. Sequent represents a
/// geometric sequent in the context of a chase implementation.
pub trait SequentTrait: Clone {
    /// Returns the body of the sequent.
    fn body(&self) -> Formula;
    /// Returns the head of the sequent.
    fn head(&self) -> Formula;
}

/// ## Selector
/// Selector is the trait for implementing a strategy for picking sequents int he context of a chase
/// implementation. The selector returns the next sequent to process.
pub trait SelectorTrait: Clone + Iterator {
    fn new(sequents: Vec<Self::Item>) -> Self;
}

/// ## Bounder
/// Bounder is the trait for implementing a strategy for bounding the models generated by chase.
pub trait BounderTrait {
    /// Returns true if the given observation is outside the bounds of the given model (the model
    /// needs to be bounded).
    fn bound<M: ModelTrait>(&self, model: &M, observation: &Observation<M::TermType>) -> bool;
}

/// ## Evaluator
/// Evaluator is the trait that binds an implementation of a sequent to an implementation of a
/// model.
pub trait EvaluatorTrait<'s, Sel: SelectorTrait<Item=&'s Self::Sequent>, B: BounderTrait> {
    type Sequent: 's + SequentTrait;
    type Model: ModelTrait;
    fn evaluate(&self
                , model: &Self::Model
                , selector: &mut Sel
                , bounder: Option<&B>) -> Option<Vec<Either<Self::Model, Self::Model>>>;
}

pub trait StrategyTrait<'s, S: 's + SequentTrait, M: ModelTrait, Sel: SelectorTrait<Item=&'s S>> {
    fn empty(&self) -> bool;
    fn add(&mut self, model: M, selector: Sel);
    fn remove(&mut self) -> Option<(M, Sel)>;
}

/// Given an initial model, a selector, an evaluator and possibly a bounder, runs the chase and
/// returns the resulting models. The resulting list of models is empty if the theory is not
/// satisfiable.
pub fn solve_all<'s, S, M, Sel, Stg, E, B>(strategy: &mut Stg, evaluator: &E, bounder: Option<&B>) -> Vec<M>
    where S: 's + SequentTrait,
          M: ModelTrait,
          Sel: SelectorTrait<Item=&'s S>,
          Stg: StrategyTrait<'s, S, M, Sel>,
          E: EvaluatorTrait<'s, Sel, B, Sequent=S, Model=M>,
          B: BounderTrait {
    let mut result: Vec<M> = Vec::new();
    while !strategy.empty() {
        solve(strategy, evaluator, bounder, |m| result.push(m));
    }
    result
}

/// Given an initial model, a selector, an evaluator and possibly a bounder, runs the chase and
/// returns the resulting models. The resulting list of models is empty if the theory is not
/// satisfiable.
pub fn solve<'s, S, M, Sel, Stg, E, B>(strategy: &mut Stg, evaluator: &E, bounder: Option<&B>, mut consumer: impl FnMut(M))
    where S: 's + SequentTrait,
          M: ModelTrait,
          Sel: SelectorTrait<Item=&'s S>,
          Stg: StrategyTrait<'s, S, M, Sel>,
          E: EvaluatorTrait<'s, Sel, B, Sequent=S, Model=M>,
          B: BounderTrait {
    let (base_model, mut selector) = strategy.remove().unwrap();
    let base_id = &base_model.get_id();
    //span!(tracing::Level::TRACE, "evaluate", id = base_id);
    let models = evaluator.evaluate(&base_model, &mut selector, bounder);

    if let Some(models) = models {
        if !models.is_empty() {
            models.into_iter().for_each(|m| {
                if let Either::Left(model) = m {
                    info!({
                              event = super::trace::NEW_MODEL_EVENT,
                              model_id = &model.get_id(),
                              parent = base_id,
                              model = tracing::field::display(&model)
                          }, "chase step applied");
                    strategy.add(model, selector.clone());
                } else if let Either::Right(model) = m {
                    info!({
                              event = super::trace::NEW_MODEL_EVENT,
                              model_id = &model.get_id(),
                              parent = base_id,
                              model = tracing::field::display(&model)
                          }, "chase step applied");
                    strategy.add(model, selector.clone());
                }
            });
        } else {
            info!({ event_type = "model_found", id = &base_id, model = tracing::field::display(&base_model) }, "model found");
            consumer(base_model);
        }
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
