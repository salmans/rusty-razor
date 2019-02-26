use std::fmt;
use crate::formula::syntax::*;
use crate::formula::syntax::Symbol;
use std::collections::HashSet;
use itertools::Either;
use std::hash::Hash;

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

pub trait WitnessTerm: Clone + Eq + Hash + fmt::Display + PartialEq {
    type ElementType;
}

/// ## Witness Term
/// Witness terms are variable free terms that provide provenance information to justify elements
/// of models.
#[derive(Clone, Eq, Hash)]
pub enum BasicWitnessTerm {
    /// ### Element
    /// Elements are treated as witness terms.
    /// > **Note:** Elements are special case of witness constants.
    Elem { element: E },

    /// ### Constant
    /// Constant witness term
    Const { constant: C },

    /// ### Function Application
    /// Complex witness term, made by applying a function to a list of witness terms.
    App { function: Func, terms: Vec<BasicWitnessTerm> },
}

impl BasicWitnessTerm {
    pub fn equals(self, rhs: BasicWitnessTerm) -> BasicObservation {
        BasicObservation::Identity { left: self, right: rhs }
    }
}

impl WitnessTerm for BasicWitnessTerm {
    type ElementType = E;
}

impl fmt::Display for BasicWitnessTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            BasicWitnessTerm::Elem { element } => write!(f, "{}", element),
            BasicWitnessTerm::Const { constant } => write!(f, "{}", constant),
            BasicWitnessTerm::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}[{}]", function, ts.join(", "))
            }
        }
    }
}

impl PartialEq for BasicWitnessTerm {
    fn eq(&self, other: &BasicWitnessTerm) -> bool {
        match (self, other) {
            (BasicWitnessTerm::Elem { element: e1 }, BasicWitnessTerm::Elem { element: e2 }) => e1 == e2,
            (BasicWitnessTerm::Const { constant: c1 }, BasicWitnessTerm::Const { constant: c2 }) => c1 == c2,
            (BasicWitnessTerm::App { function: f1, terms: ts1 }, BasicWitnessTerm::App { function: f2, terms: ts2 }) => {
                f1 == f2 && ts1.iter().zip(ts2).all(|(x, y)| x == y)
            }
            _ => false
        }
    }
}

impl From<C> for BasicWitnessTerm {
    fn from(constant: C) -> Self {
        BasicWitnessTerm::Const { constant }
    }
}

impl From<E> for BasicWitnessTerm {
    fn from(element: E) -> Self {
        BasicWitnessTerm::Elem { element }
    }
}

pub type BasicWitnessTerms = Vec<BasicWitnessTerm>;

impl Func {
    /// Applies the function to a list of witness terms.
    pub fn wit_app(self, terms: BasicWitnessTerms) -> BasicWitnessTerm {
        BasicWitnessTerm::App { function: self, terms }
    }
    /// Applies the function to a list of terms.
    pub fn wit_app0(self) -> BasicWitnessTerm {
        BasicWitnessTerm::App { function: self, terms: vec![] }
    }
    /// Applies the (unary) function to a witness term.
    pub fn wit_app1(self, first: BasicWitnessTerm) -> BasicWitnessTerm {
        BasicWitnessTerm::App { function: self, terms: vec![first] }
    }
    /// Applies the (binary) predicate to two witness terms.
    pub fn wit_app2(self, first: BasicWitnessTerm, second: BasicWitnessTerm) -> BasicWitnessTerm {
        BasicWitnessTerm::App { function: self, terms: vec![first, second] }
    }
    /// Applies the (ternary) function to three witness terms.
    pub fn wit_app3(self, first: BasicWitnessTerm, second: BasicWitnessTerm, third: BasicWitnessTerm) -> BasicWitnessTerm {
        BasicWitnessTerm::App { function: self, terms: vec![first, second, third] }
    }
    /// Applies the (4-ary) function to four witness terms.
    pub fn wit_app4(self, first: BasicWitnessTerm, second: BasicWitnessTerm, third: BasicWitnessTerm, fourth: BasicWitnessTerm) -> BasicWitnessTerm {
        BasicWitnessTerm::App { function: self, terms: vec![first, second, third, fourth] }
    }
    /// Applies the (5-ary) function to five witness terms.
    pub fn wit_app5(self, first: BasicWitnessTerm, second: BasicWitnessTerm, third: BasicWitnessTerm, fourth: BasicWitnessTerm, fifth: BasicWitnessTerm) -> BasicWitnessTerm {
        BasicWitnessTerm::App { function: self, terms: vec![first, second, third, fourth, fifth] }
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
    pub fn app(self, terms: Vec<BasicWitnessTerm>) -> BasicObservation {
        BasicObservation::Fact { relation: self, terms }
    }
    /// Applies the relation to a list of terms.
    pub fn app0(self) -> BasicObservation {
        BasicObservation::Fact { relation: self, terms: vec![] }
    }
    /// Applies the (unary) relation to a witness term.
    pub fn app1(self, first: BasicWitnessTerm) -> BasicObservation {
        BasicObservation::Fact { relation: self, terms: vec![first] }
    }
    /// Applies the (binary) predicate to two witness terms.
    pub fn app2(self, first: BasicWitnessTerm, second: BasicWitnessTerm) -> BasicObservation {
        BasicObservation::Fact { relation: self, terms: vec![first, second] }
    }
    /// Applies the (ternary) relation to three witness terms.
    pub fn app3(self, first: BasicWitnessTerm, second: BasicWitnessTerm, third: BasicWitnessTerm) -> BasicObservation {
        BasicObservation::Fact { relation: self, terms: vec![first, second, third] }
    }
    /// Applies the (4-ary) relation to four witness terms.
    pub fn app4(self, first: BasicWitnessTerm, second: BasicWitnessTerm, third: BasicWitnessTerm, fourth: BasicWitnessTerm) -> BasicObservation {
        BasicObservation::Fact { relation: self, terms: vec![first, second, third, fourth] }
    }
    /// Applies the (5-ary) relation to five witness terms.
    pub fn app5(self, first: BasicWitnessTerm, second: BasicWitnessTerm, third: BasicWitnessTerm, fourth: BasicWitnessTerm, fifth: BasicWitnessTerm) -> BasicObservation {
        BasicObservation::Fact { relation: self, terms: vec![first, second, third, fourth, fifth] }
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

pub trait Observation: PartialEq + Eq + Hash + Clone + fmt::Display {
    type TermType: WitnessTerm;
}

/// ## Observation
/// Observations are true positive *facts* that are true in the model.
#[derive(PartialEq, Eq, Hash, Clone)]
pub enum BasicObservation {
    /// Relational fact
    Fact { relation: Rel, terms: BasicWitnessTerms },
    /// Identity fact
    Identity { left: BasicWitnessTerm, right: BasicWitnessTerm },
}

impl Observation for BasicObservation {
    type TermType = BasicWitnessTerm;
}

impl<'t> fmt::Display for BasicObservation {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            BasicObservation::Fact { relation, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "<{}({})>", relation, ts.join(", "))
            }
            BasicObservation::Identity { left, right } => write!(f, "<{} = {}>", left, right),
        }
    }
}

/// ## Model
/// Model is the common trait for various possible implementations of first order models, returned
/// by the chase.
pub trait Model: Clone + fmt::Display + ToString {
    type ObservationType: Observation;

    /// Returns the domain of this model.
    fn domain(&self) -> HashSet<&E>;
    /// Returns the set of observation facts that are true in this model.
    fn facts(&self) -> HashSet<&Self::ObservationType>;
    /// Makes the given observation hold in the model.
    fn observe(&mut self, observation: &Self::ObservationType);
    /// Returns true if the given observation holds in the model.
    fn is_observed(&self, observation: &Self::ObservationType) -> bool;
    /// Returns a set of all witness terms for the given element.
    fn witness(&self, element: &E) -> HashSet<&<Self::ObservationType as Observation>::TermType>;
    /// Returns the element, associated with the given witness term.
    fn element(&self, witness: &<Self::ObservationType as Observation>::TermType) -> Option<E>;
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
    fn bound<M: Model>(&self, model: &M, observation: &BasicObservation) -> bool;
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
// TODO: consider implementing Strategy as a priority queue.
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
        // TODO selector below should not be cloned
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
    fn test_witness_app() {
        assert_eq!("f[]", f().wit_app0().to_string());
        assert_eq!("f['c]", f().wit_app1(_c_()).to_string());
        assert_eq!("f[g[]]", f().wit_app1(g().wit_app0()).to_string());
        assert_eq!("f['c, g['d]]", f().wit_app2(_c_(), g().wit_app1(_d_())).to_string());
    }

    #[test]
    fn test_rel() {
        assert_eq!(_R_(), R().into());
        assert_eq!("R", _R_().to_string());
    }

    #[test]
    fn test_observation() {
        assert_eq!("<R()>", _R_().app0().to_string());
        assert_eq!("<R(e#0)>", _R_().app1(_e_0()).to_string());
        assert_eq!("<R(e#0, e#1, e#2)>", _R_().app3(_e_0(), _e_1(), _e_2()).to_string());
        assert_eq!("<e#0 = e#1>", _e_0().equals(_e_1()).to_string());
    }
}