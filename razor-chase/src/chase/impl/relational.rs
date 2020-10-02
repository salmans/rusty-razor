//! Implements [the chase] based on relational algebra.
//!
//! [the chase]: ../../index.html#the-chase
//!
mod attribute;
mod evaluator;
mod expression;
mod memo;
mod model;
mod preprocessor;
mod sequent;

use crate::chase::{r#impl::basic::WitnessTerm, Observation, Rel, WitnessTermTrait, E};
use anyhow::{bail, Result};
pub use evaluator::Evaluator;
pub use model::Model;
pub use preprocessor::PreProcessor;
use razor_fol::syntax;
pub use sequent::Sequent;
use std::collections::HashMap;

mod constants {
    use razor_fol::syntax;

    /// The naming prefix of existential attributes and variables in relational formulae.
    pub(super) const EXISTENTIAL_PREFIX: &str = "?";

    /// The naming prefix of equational attributes and variables in relational formulae.
    pub(super) const EQUATIONAL_PREFIX: &str = "~";

    /// The naming prefix of functional predicates created during relationalization
    pub(super) const FUNCTIONAL_PREDICATE_PREFIX: &str = "$";

    /// Seperators in different parts of attribute and variable names.
    pub(super) const SEPERATOR: &str = ":";

    /// Is the name of the database instance for domain of elements.
    pub(super) const DOMAIN: &str = "$$domain";

    /// Is the name of the database instance for the equality relation.
    pub(super) const EQUALITY: &str = razor_fol::syntax::EQ_SYM;

    // Create database instance names from symbols:
    #[inline]
    pub(super) fn constant_instance_name(c: &syntax::C) -> String {
        format!("${}", c)
    }

    #[inline]
    pub(super) fn function_instance_name(f: &syntax::F) -> String {
        format!("${}", f)
    }

    #[inline]
    pub(super) fn predicate_instance_name(p: &syntax::Pred) -> String {
        p.to_string()
    }
}

/// Is the type of unnamed tuples used in database instances.
type Tuple = Vec<crate::chase::E>;

/// Is a named tuple where every element is identified by an attribute.
type NamedTuple<'a> = HashMap<&'a attribute::Attribute, crate::chase::E>;

/// Returns an empty named tuple.
fn empty_named_tuple<'a>() -> NamedTuple<'a> {
    HashMap::new()
}

/// Is the symbol associated to a relational instance.
#[derive(Hash, PartialEq, Eq, Clone, PartialOrd, Ord, Debug)]
enum Symbol {
    /// Constant symbol
    Const(syntax::C),

    /// Function symbol
    Func { symbol: syntax::F, arity: u8 },

    /// Predicate symbol
    Pred { symbol: syntax::Pred, arity: u8 },

    /// Equality symbol
    Equality,

    /// Domain of elements
    Domain,
}

impl Symbol {
    /// Creates a witness term from symbol, given a list of arguments `E`.
    fn witness(&self, args: &[E]) -> Result<WitnessTerm> {
        match self {
            Symbol::Const(symbol) => {
                assert!(args.len() == 0);

                Ok(WitnessTerm::from(symbol.clone()))
            }
            Symbol::Func { symbol, arity } => {
                assert_eq!(args.len() as u8, *arity);

                let witness = symbol
                    .clone()
                    .app(args.iter().map(|e| e.clone().into()).collect());
                Ok(witness)
            }
            _ => bail!("cannot create witness term for symbol"),
        }
    }

    /// Creates an observation from the receiver symbol with a slice of `E` as arguments.
    fn observation(&self, args: &[E]) -> Option<Observation<WitnessTerm>> {
        match self {
            Symbol::Pred { symbol, arity } => {
                assert_eq!(args.len() as u8, *arity);

                Some(
                    Rel::from(symbol.clone())
                        .app(args.iter().map(|e| WitnessTerm::from(e.clone())).collect()),
                )
            }
            Symbol::Equality => {
                assert_eq!(args.len(), 2);

                Some(WitnessTerm::from(args[0].clone()).equals(args[1].clone().into()))
            }
            Symbol::Const(c) => {
                assert_eq!(args.len(), 1);

                Some(WitnessTerm::from(c.clone()).equals(WitnessTerm::from(args[0])))
            }
            Symbol::Func { symbol, ref arity } => {
                assert_eq!(args.len() as u8, arity + 1);

                let last = args[*arity as usize];
                let app = symbol.clone().app(
                    args[0..(*arity as usize)]
                        .iter()
                        .map(WitnessTerm::from)
                        .collect(),
                );
                Some(app.equals(last.into()))
            }
            Symbol::Domain => None, // the Domain instance is used only for book-keeping
        }
    }
}

#[cfg(test)]
mod tests {
    // use super::*;
    // use razor_fol::{formula, v};

    // #[test]
    // fn test_new_sequent() {
    //     let mut database = relalg::Database::new();
    //     let p = database.add_relation::<Tup>("P").unwrap();
    //     let q = database.add_relation::<Tup>("Q").unwrap();
    //     database.insert(&p, vec![vec![E(1)], vec![E(2)]].into());
    //     database.insert(&q, vec![vec![E(2)]].into());

    //     let sequent = Sequent::try_from(&formula!([P(x)] -> [Q(x)])).unwrap();
    //     assert_eq!(1, sequent.branches.len());
    //     assert_eq!(
    //         Attributes::from(vec![v!(x)]),
    //         sequent.branches[0].attributes
    //     );
    //     assert_eq!(Attributes::from(vec![]), sequent.branches[0].projected);
    //     assert_eq!(
    //         relalg::Tuples::from(vec![vec![E(1)]]),
    //         database.evaluate(&sequent.branches[0].expression).unwrap()
    //     );
    // }

    // #[test]
    // fn test_balance_sequent() {
    //     let mut database = relalg::Database::new();
    //     let p = database.add_relation::<Tup>("P").unwrap();
    //     let q = database.add_relation::<Tup>("Q").unwrap();
    //     let f = database.add_relation::<Tup>("$f").unwrap();
    //     let domain = database.add_relation::<Tup>("$$domain").unwrap();
    //     let eq = database.add_relation::<Tup>("=").unwrap();

    //     database.insert(&p, vec![vec![E(1)]].into());
    //     database.insert(&domain, vec![vec![E(1)], vec![E(2)], vec![E(3)]].into());
    //     database.insert(
    //         &eq,
    //         vec![vec![E(1), E(1)], vec![E(2), E(2)], vec![E(3), E(3)]].into(),
    //     );

    //     let model = Model {
    //         id: 1,
    //         element_index: 4,
    //         domain: HashSet::new(),
    //         database,
    //     };

    //     let sequent = Sequent::try_from(&formula!([P(x)] -> [Q(f(f(x)))])).unwrap();
    //     // let sequent = Sequent::try_from(&formula!([P(x)] -> [Q(f(x))])).unwrap();
    //     let models = sequent.balance(&model).unwrap();

    //     assert_eq!(
    //         relalg::Tuples::from(vec![vec![E(4)]]),
    //         models[0].database.evaluate(&q).unwrap()
    //     );
    //     assert_eq!(
    //         relalg::Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)]]),
    //         models[0].database.evaluate(&f).unwrap()
    //     );
    // }

    // #[test]
    // fn test_balance_sequent() {
    //     let mut database = relalg::Database::new();
    //     let p = database.add_relation::<Tup>("P").unwrap();
    //     let q = database.add_relation::<Tup>("Q").unwrap();
    //     let r = database.add_relation::<Tup>("R").unwrap();
    //     let domain = database.add_relation::<Tup>("$$domain").unwrap();
    //     let eq = database.add_relation::<Tup>("=").unwrap();

    //     database.insert(&p, vec![vec![E(1)], vec![E(2)], vec![E(3)]].into());
    //     database.insert(&q, vec![vec![E(2)]].into());
    //     database.insert(&domain, vec![vec![E(1)], vec![E(2)], vec![E(3)]].into());
    //     database.insert(
    //         &eq,
    //         vec![vec![E(1), E(1)], vec![E(2), E(2)], vec![E(3), E(3)]].into(),
    //     );

    //     let model = Model {
    //         id: 1,
    //         element_index: 0,
    //         domain: HashSet::new(),
    //         database,
    //     };

    //     let sequent = Sequent::try_from(&formula!([P(x)] -> [{[Q(x)] & [R(x)]} | {P(x)}])).unwrap();
    //     let models = sequent.balance(&model).unwrap();

    //     assert_eq!(
    //         relalg::Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)]]),
    //         models[0].database.evaluate(&q).unwrap()
    //     );
    //     assert_eq!(
    //         relalg::Tuples::from(vec![vec![E(1)], vec![E(2)], vec![E(3)]]),
    //         models[0].database.evaluate(&r).unwrap()
    //     );

    //     assert_eq!(
    //         relalg::Tuples::from(vec![vec![E(2)]]),
    //         models[1].database.evaluate(&q).unwrap()
    //     );
    // }
}
