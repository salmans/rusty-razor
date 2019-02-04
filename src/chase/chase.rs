use std::fmt;
use crate::formula::syntax::*;
use crate::formula::syntax::Symbol;
use std::collections::HashSet;
use itertools::Either;

/// ### Element
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
#[derive(Clone, Eq, Hash)]
pub enum WitnessTerm {
    /// ### Element
    /// Elements are treated as witness terms.
    /// > **Note:** Elements are special case of witness constants.
    Elem { element: E },

    /// ### Constant
    /// Constant witness term
    Const { constant: C },

    /// ### Function Application
    /// Complex witness term, made by applying a function to a list of witness terms.
    App { function: Func, terms: Vec<WitnessTerm> },
}

impl WitnessTerm {
    pub fn equals(self, rhs: WitnessTerm) -> Observation {
        Observation::Identity { left: self, right: rhs }
    }
}

impl fmt::Display for WitnessTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            WitnessTerm::Elem { element } => write!(f, "{}", element),
            WitnessTerm::Const { constant } => write!(f, "{}", constant),
            WitnessTerm::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}[{}]", function, ts.join(", "))
            }
        }
    }
}

impl PartialEq for WitnessTerm {
    fn eq(&self, other: &WitnessTerm) -> bool {
        match (self, other) {
            (WitnessTerm::Elem { element: e1 }, WitnessTerm::Elem { element: e2 }) => e1 == e2,
            (WitnessTerm::Const { constant: c1 }, WitnessTerm::Const { constant: c2 }) => c1 == c2,
            (WitnessTerm::App { function: f1, terms: ts1 }, WitnessTerm::App { function: f2, terms: ts2 }) => {
                f1 == f2 && ts1.iter().zip(ts2).all(|(x, y)| x == y)
            }
            _ => false
        }
    }
}

impl From<C> for WitnessTerm {
    fn from(constant: C) -> Self {
        WitnessTerm::Const { constant }
    }
}

impl From<E> for WitnessTerm {
    fn from(element: E) -> Self {
        WitnessTerm::Elem { element }
    }
}

pub type WitnessTerms = Vec<WitnessTerm>;

impl Func {
    /// Applies the function to a list of witness terms.
    pub fn wit_app(self, terms: WitnessTerms) -> WitnessTerm {
        WitnessTerm::App { function: self, terms }
    }
    /// Applies the function to a list of terms.
    pub fn wit_app0(self) -> WitnessTerm {
        WitnessTerm::App { function: self, terms: vec![] }
    }
    /// Applies the (unary) function to a witness term.
    pub fn wit_app1(self, first: WitnessTerm) -> WitnessTerm {
        WitnessTerm::App { function: self, terms: vec![first] }
    }
    /// Applies the (binary) predicate to two witness terms.
    pub fn wit_app2(self, first: WitnessTerm, second: WitnessTerm) -> WitnessTerm {
        WitnessTerm::App { function: self, terms: vec![first, second] }
    }
    /// Applies the (ternary) function to three witness terms.
    pub fn wit_app3(self, first: WitnessTerm, second: WitnessTerm, third: WitnessTerm) -> WitnessTerm {
        WitnessTerm::App { function: self, terms: vec![first, second, third] }
    }
    /// Applies the (4-ary) function to four witness terms.
    pub fn wit_app4(self, first: WitnessTerm, second: WitnessTerm, third: WitnessTerm, fourth: WitnessTerm) -> WitnessTerm {
        WitnessTerm::App { function: self, terms: vec![first, second, third, fourth] }
    }
    /// Applies the (5-ary) function to five witness terms.
    pub fn wit_app5(self, first: WitnessTerm, second: WitnessTerm, third: WitnessTerm, fourth: WitnessTerm, fifth: WitnessTerm) -> WitnessTerm {
        WitnessTerm::App { function: self, terms: vec![first, second, third, fourth, fifth] }
    }
}

/// ### Relation
/// Relations are semantic counterparts of predicates and are used to construct observations.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Rel(pub String);

impl Rel {
    pub fn new(name: &str) -> Rel {
        Rel(name.to_string())
    }

    /// Applies the relation to a list of witness terms.
    pub fn app(self, terms: Vec<WitnessTerm>) -> Observation {
        Observation::Fact { relation: self, terms }
    }
    /// Applies the relation to a list of terms.
    pub fn app0(self) -> Observation {
        Observation::Fact { relation: self, terms: vec![] }
    }
    /// Applies the (unary) relation to a witness term.
    pub fn app1(self, first: WitnessTerm) -> Observation {
        Observation::Fact { relation: self, terms: vec![first] }
    }
    /// Applies the (binary) predicate to two witness terms.
    pub fn app2(self, first: WitnessTerm, second: WitnessTerm) -> Observation {
        Observation::Fact { relation: self, terms: vec![first, second] }
    }
    /// Applies the (ternary) relation to three witness terms.
    pub fn app3(self, first: WitnessTerm, second: WitnessTerm, third: WitnessTerm) -> Observation {
        Observation::Fact { relation: self, terms: vec![first, second, third] }
    }
    /// Applies the (4-ary) relation to four witness terms.
    pub fn app4(self, first: WitnessTerm, second: WitnessTerm, third: WitnessTerm, fourth: WitnessTerm) -> Observation {
        Observation::Fact { relation: self, terms: vec![first, second, third, fourth] }
    }
    /// Applies the (5-ary) relation to five witness terms.
    pub fn app5(self, first: WitnessTerm, second: WitnessTerm, third: WitnessTerm, fourth: WitnessTerm, fifth: WitnessTerm) -> Observation {
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

/// ### Observation
/// Observations are true positive *facts* that are true in the model.
#[derive(PartialEq, Eq, Hash, Clone)]
pub enum Observation {
    /// Relational fact
    Fact { relation: Rel, terms: WitnessTerms },
    /// Identity fact
    Identity { left: WitnessTerm, right: WitnessTerm },
}

impl<'t> fmt::Display for Observation {
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

pub trait Model: Clone + fmt::Display + ToString {
    fn domain(&self) -> HashSet<&E>;
    fn facts(&self) -> HashSet<&Observation>;
    fn observe(&mut self, observation: &Observation);
    fn is_observed(&self, observation: &Observation) -> bool;
    fn witness(&self, element: &E) -> HashSet<&WitnessTerm>;
    fn element(&self, witness: &WitnessTerm) -> Option<E>;
}

pub trait Sequent: Clone {
    fn left(&self) -> Formula;
    fn right(&self) -> Formula;
}

pub trait Selector: Clone + Iterator {}

pub trait Bounder {
    fn bound<M: Model>(&self, model: &M, observation: &Observation) -> bool;
}

pub trait Evaluator<S: Sequent, M: Model, Sel: Selector<Item=S>, B: Bounder> {
    fn evaluate(&self
                , model: &M
                , selector: Sel
                , bounder: Option<&B>) -> Option<Vec<Either<M, M>>>;
}

pub struct StrategyNode<S: Sequent, M: Model, Sel: Selector<Item=S>> {
    pub model: M,
    pub selector: Sel,
}

impl <S: Sequent, M: Model, Sel: Selector<Item=S>> StrategyNode<S, M, Sel> {
    pub fn new(model: M, selector: Sel) -> StrategyNode<S, M, Sel> {
        StrategyNode { model, selector }
    }
}

// TODO: consider implementing Strategy as a priority queue.
pub trait Strategy<S: Sequent, M: Model, Sel: Selector<Item=S>> {
    fn empty(&self) -> bool;
    fn add(&mut self, node: StrategyNode<S, M, Sel>);
    fn remove(&mut self) -> Option<StrategyNode<S, M, Sel>>;
}

pub fn solve_all<S: Sequent
    , M: Model
    , Sel: Selector<Item=S>
    , E: Evaluator<S, M, Sel, B>
    , B: Bounder>(
    mut strategy: Box<Strategy<S, M, Sel>>
    , evaluator: Box<E>
    , bounder: Option<&B>) -> Vec<M> {
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