pub mod r#impl;
pub mod selector;
pub mod strategy;
pub mod bounder;

use crate::formula::syntax::{*, Symbol};
use itertools::Either;
use std::{collections::HashSet, fmt, hash::Hash};

/// ## Element
/// Element symbols represent elements of models.
#[derive(PartialEq, PartialOrd, Eq, Hash, Clone, Ord)]
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
pub trait WitnessTerm: Clone + Eq + Hash + fmt::Display + PartialEq + FuncApp {
    /// The internal representation of an element when implementing a WitnessTerm.
    type ElementType;

    /// Constructs an Identity observation for two witness terms.
    fn equals(self, rhs: Self) -> Observation<Self> {
        Observation::Identity { left: self, right: rhs }
    }
}

/// ## Relation
/// Relations are semantic counterparts of predicates and are used to construct observations.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Rel(pub String);

impl Rel {
    pub fn new(name: &str) -> Rel {
        Rel(name.to_string())
    }
    /// Applies the relation to a list of witness terms.
    pub fn app<T: WitnessTerm>(self, terms: Vec<T>) -> Observation<T> {
        Observation::Fact { relation: self, terms }
    }
    /// Applies the relation to a list of terms.
    pub fn app0<T: WitnessTerm>(self) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![] }
    }
    /// Applies the (unary) relation to a witness term.
    pub fn app1<T: WitnessTerm>(self, first: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first] }
    }
    /// Applies the (binary) predicate to two witness terms.
    pub fn app2<T: WitnessTerm>(self, first: T, second: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second] }
    }
    /// Applies the (ternary) relation to three witness terms.
    pub fn app3<T: WitnessTerm>(self, first: T, second: T, third: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second, third] }
    }
    /// Applies the (4-ary) relation to four witness terms.
    pub fn app4<T: WitnessTerm>(self, first: T, second: T, third: T, fourth: T) -> Observation<T> {
        Observation::Fact { relation: self, terms: vec![first, second, third, fourth] }
    }
    /// Applies the (5-ary) relation to five witness terms.
    pub fn app5<T: WitnessTerm>(self, first: T, second: T, third: T, fourth: T, fifth: T) -> Observation<T> {
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

impl Symbol for Rel {}

/// ## Observation
/// Observations are true positive *facts* that are true in the model.
#[derive(PartialEq, Eq, Hash, Clone)]
pub enum Observation<T: WitnessTerm> {
    /// Relational fact
    Fact { relation: Rel, terms: Vec<T> },
    /// Identity fact
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

/// ## Model
/// Model is the common trait for various possible implementations of first order models, returned
/// by the chase.
pub trait Model: Clone + fmt::Display + ToString {
    type TermType: WitnessTerm;

    /// Returns the domain of this model.
    fn domain(&self) -> HashSet<&E>;
    /// Returns the set of observation facts that are true in this model.
    fn facts(&self) -> HashSet<&Observation<Self::TermType>>;
    /// Makes the given observation hold in the model.
    fn observe(&mut self, observation: &Observation<Self::TermType>);
    /// Returns true if the given observation holds in the model.
    fn is_observed(&self, observation: &Observation<Self::TermType>) -> bool;
    /// Returns a set of all witness terms for the given element.
    fn witness(&self, element: &E) -> HashSet<&Self::TermType>;
    /// Returns the element, associated with the given witness term.
    fn element(&self, witness: &Self::TermType) -> Option<E>;
}

/// ## Sequent
/// Sequent is the common trait for various implementations of sequents. Sequent represents a
/// geometric sequent in the context of a chase implementation.
pub trait Sequent: Clone {
    /// Returns the body of the sequent.
    fn body(&self) -> Formula;
    /// Returns the head of the sequent.
    fn head(&self) -> Formula;
}

/// ## Selector
/// Selector is the trait for implementing a strategy for picking sequents int he context of a chase
/// implementation. The selector returns the next sequent to process.
pub trait Selector: Clone + Iterator {
    fn new(sequents: Vec<Self::Item>) -> Self;
}

/// ## Bounder
/// Bounder is the trait for implementing a strategy for bounding the models generated by chase.
pub trait Bounder {
    /// Returns true if the given observation is outside the bounds of the given model (the model
    /// needs to be bounded).
    fn bound<M: Model>(&self, model: &M, observation: &Observation<M::TermType>) -> bool;
}

/// ## Evaluator
/// Evaluator is the trait that binds an implementation of a sequent to an implementation of a
/// model.
pub trait Evaluator<Sel: Selector<Item=Self::Sequent>, B: Bounder> {
    type Sequent: Sequent;
    type Model: Model;
    fn evaluate(&self
                , model: &Self::Model
                , selector: Sel
                , bounder: Option<&B>) -> Option<Vec<Either<Self::Model, Self::Model>>>;
}

/// ## StrategyNode
/// StrategyNode is used to keep track of intermediate chase computations.
pub struct StrategyNode<S: Sequent, M: Model, Sel: Selector<Item=S>> {
    pub model: M,
    pub selector: Sel,
}

impl<S: Sequent, M: Model, Sel: Selector<Item=S>> StrategyNode<S, M, Sel> {
    pub fn new(model: M, selector: Sel) -> StrategyNode<S, M, Sel> {
        StrategyNode { model, selector }
    }
}

/// ## Strategy
/// Strategy is the trait for selecting the next branch of chase to process.
// TODO: implement Strategy as a priority queue.
pub trait Strategy<S: Sequent, M: Model, Sel: Selector<Item=S>> {
    fn empty(&self) -> bool;
    fn add(&mut self, node: StrategyNode<S, M, Sel>);
    fn remove(&mut self) -> Option<StrategyNode<S, M, Sel>>;
}

/// Given an initial model, a selector, an evaluator and possibly a bounder, runs the chase and
/// returns the resulting models. The resulting list of models is empty if the theory is not
/// satisfiable.
pub fn solve_all<S: Sequent, M: Model, Sel: Selector<Item=S>, E: Evaluator<Sel, B, Sequent=S, Model=M>, B: Bounder>(
    mut strategy: Box<Strategy<S, M, Sel>>, evaluator: Box<E>, bounder: Option<&B>) -> Vec<M> {
    let mut result: Vec<M> = Vec::new();
    while !strategy.empty() {
        let node = strategy.remove().unwrap();
        // TODO selector below shouldn't be cloned
        let models = evaluator.evaluate(&node.model, node.selector.clone(), bounder);
        if let Some(models) = models {
            if !models.is_empty() {
                models.into_iter().for_each(|m| {
                    if let Either::Left(model) = m {
                        strategy.add(StrategyNode { model, selector: node.selector.clone() });
                    } else if let Either::Right(model) = m {
                        result.push(model);
                    }
                });
            } else {
                result.push(node.model.clone()); // can we return pointers to models?
            }
        }
    }
    return result;
}

//// Tests -------------------------------------
#[cfg(test)]
mod test_chase {
    use crate::test_prelude::*;

    #[test]
    fn test_witness_const() {
        assert_eq!(_a_(), _a().into());
        assert_eq!("'a", _a_().to_string());
    }

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

    #[test]
    fn test_observation() {
        assert_eq!("<R(e#0)>", _R_().app1(_e_0()).to_string());
        assert_eq!("<R(e#0, e#1, e#2)>", _R_().app3(_e_0(), _e_1(), _e_2()).to_string());
        assert_eq!("<e#0 = e#1>", _e_0().equals(_e_1()).to_string());
    }
}
