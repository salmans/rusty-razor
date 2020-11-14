use super::{
    attribute::{Attribute, AttributeList},
    constants::*,
    expression::make_expression,
    memo::ViewMemo,
    symbol::Symbol,
    Error, Tuple,
};
use crate::chase::SequentTrait;
use codd::expression as rel_exp;
use razor_fol::{
    syntax::{symbol::Generator, Formula, Pred, Term, C, F},
    transform::relationalize,
};

/// Represents an atomic formula in the head of a `Sequent`.
#[derive(Hash, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct Atom {
    /// The relational predicate symbol of the atom.
    symbol: Symbol,

    /// The list of attributes of the atom.
    attributes: AttributeList,
}

impl Atom {
    /// Creates a new atom from a given relational predicate symbol and a list of attributes.
    fn new(symbol: &Symbol, attributes: AttributeList) -> Self {
        Self {
            symbol: symbol.clone(),
            attributes,
        }
    }

    /// Returns the relation symbol of the atom.
    #[inline]
    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }

    /// Returns the relational attributes of the atom.
    #[inline]
    pub fn attributes(&self) -> &AttributeList {
        &self.attributes
    }
}

/// Represents a branch in the head of a `Sequent`.
pub(super) type Branch = Vec<Atom>;

/// Represents a sequent for the chase.
#[derive(Clone)]
pub struct Sequent {
    /// Is the branches in the head of the sequent, used to infer new facts that must be true
    /// in the a `Model`.
    branches: Vec<Branch>,

    /// Is the attributes shared in the body and the head of the sequent.
    attributes: AttributeList,

    /// Is the relational expression corresponding to evaluating this sequent in the body.
    /// In the general case, this expression is the difference between the expression in the body
    /// and the expression in the head.
    pub expression: rel_exp::Mono<Tuple>,

    /// The body of the implication from which the sequent was made.
    body_formula: Formula,

    /// The head of the implication from which the sequent was made.
    head_formula: Formula,
}

impl Sequent {
    /// Returns the relational expression of the sequent.
    #[inline]
    pub fn expression(&self) -> &rel_exp::Mono<Tuple> {
        &self.expression
    }

    /// Returns the branches of the sequent.
    #[inline]
    pub(super) fn branches(&self) -> &[Branch] {
        &self.branches
    }

    /// Returns the relational attributes of the sequent.
    #[inline]
    pub(super) fn attributes(&self) -> &AttributeList {
        &self.attributes
    }

    pub(super) fn new(formula: &Formula, memo: Option<&mut ViewMemo>) -> Result<Self, Error> {
        use itertools::Itertools;

        #[inline]
        fn implies_parts(formula: &Formula) -> Result<(&Formula, &Formula), Error> {
            if let Formula::Implies { left, right } = formula {
                Ok((left, right))
            } else {
                Err(Error::BadSequentFormula {
                    formula: formula.clone(),
                })
            }
        }

        let (left, right) = implies_parts(formula)?;

        // relationalize and expand equalities of `left` and `right`:
        let left_er = expand_equality(&relationalize(left)?)?;
        let right_r = relationalize(right)?;
        let branches = build_branches(right_r.formula())?; // relationalized right is enough for building branches
        let right_er = expand_equality(&right_r)?;

        let right_attrs = AttributeList::try_from_formula(right_er.formula())?.universals();
        let range = Vec::from(&right_attrs);

        // apply range restriction:
        let left_rr = relationalize::range_restrict(&left_er, &range, DOMAIN)?;
        let right_rr = relationalize::range_restrict(&right_er, &range, DOMAIN)?;

        let left_attrs =
            AttributeList::try_from_formula(left_rr.formula())?.intersect(&right_attrs);

        let branches = if branches.iter().any(|branch| branch.is_empty()) {
            vec![vec![]] // logically the right is true
        } else {
            // Remove duplicate atoms is necessary for correctness:
            branches
                .into_iter()
                .map(|branch| branch.into_iter().unique().collect())
                .collect()
        };

        let (left_expr, right_expr) = if let Some(memo) = memo {
            (
                memo.make_expression(left_rr.formula(), &left_attrs)?,
                memo.make_expression(right_rr.formula(), &left_attrs)?,
            )
        } else {
            (
                make_expression(left_rr.formula(), &left_attrs)?,
                make_expression(right_rr.formula(), &left_attrs)?,
            )
        };

        let expression = match &branches[..] {
            [] => left_expr,
            _ => match &branches[0][..] {
                [] => rel_exp::Mono::from(rel_exp::Empty::new()),
                _ => rel_exp::Mono::from(rel_exp::Difference::new(left_expr, right_expr)),
            },
        };

        Ok(Self {
            branches,
            attributes: left_attrs,
            expression,
            body_formula: left.clone(),
            head_formula: right.clone(),
        })
    }
}

impl SequentTrait for Sequent {
    fn body(&self) -> Formula {
        self.body_formula.clone()
    }

    fn head(&self) -> Formula {
        self.head_formula.clone()
    }
}

// Create consistent `Relationalizer` instances:
fn relationalize(formula: &Formula) -> Result<relationalize::Relational, Error> {
    let mut relationalizer = relationalize::Relationalizer::new();
    relationalizer.set_equality_symbol(EQUALITY);
    relationalizer.set_flattening_generator(Generator::new().set_prefix(EXISTENTIAL_PREFIX));
    relationalizer
        .set_predicate_generator(Generator::new().set_prefix(FUNCTIONAL_PREDICATE_PREFIX));

    relationalizer.transform(formula).map_err(|e| e.into())
}

// Create consistent `EqualityExpander` instances:
fn expand_equality(
    formula: &relationalize::Relational,
) -> Result<relationalize::Relational, Error> {
    let mut equality_expander = relationalize::EqualityExpander::new();
    equality_expander.set_equality_symbol(EQUALITY);
    equality_expander.set_equality_generator(
        Generator::new()
            .set_prefix(EQUATIONAL_PREFIX)
            .set_delimiter(SEPERATOR),
    );

    equality_expander.transform(formula).map_err(|e| e.into())
}

fn build_branches(formula: &Formula) -> Result<Vec<Vec<Atom>>, Error> {
    use std::convert::TryFrom;

    match formula {
        Formula::Top => Ok(vec![vec![]]),
        Formula::Bottom => Ok(vec![]),
        Formula::Atom { predicate, terms } => {
            let mut attributes = Vec::new();
            for term in terms {
                match term {
                    Term::Var { variable } => {
                        // calling `into_canonical` is unnecessary when branches are built before
                        // equality expansion because there are no equational attributes.
                        // (the existing algorithm)
                        attributes.push(Attribute::try_from(variable)?.into_canonical())
                    }
                    _ => return Err(Error::BadFlatTerm { term: term.clone() }),
                }
            }

            let symbol = if predicate.0 == DOMAIN {
                Symbol::Domain
            } else if predicate.0 == EQUALITY {
                Symbol::Equality
            } else if predicate.0.starts_with(CONSTANT_PREDICATE_PREFIX) {
                Symbol::Const(C(predicate.0[1..].to_string()))
            } else if predicate.0.starts_with(FUNCTIONAL_PREDICATE_PREFIX) {
                Symbol::Func {
                    symbol: F(predicate.0[1..].to_string()),
                    arity: (terms.len() - 1) as u8,
                }
            } else {
                Symbol::Pred {
                    symbol: Pred(predicate.0.to_string()),
                    arity: terms.len() as u8,
                }
            };

            Ok(vec![vec![Atom::new(&symbol, attributes.into())]])
        }
        Formula::And { left, right } => {
            let mut left = build_branches(left)?;
            let mut right = build_branches(right)?;

            if left.is_empty() {
                Ok(left)
            } else if right.is_empty() {
                Ok(right)
            } else if left.len() == 1 && right.len() == 1 {
                let mut left = left.remove(0);
                let mut right = right.remove(0);
                left.append(&mut right);
                Ok(vec![left])
            } else {
                Err(Error::BadSequentFormula {
                    formula: formula.clone(),
                })
            }
        }
        Formula::Or { left, right } => {
            let mut left = build_branches(left)?;
            let mut right = build_branches(right)?;
            left.append(&mut right);
            Ok(left)
        }
        _ => Err(Error::BadSequentFormula {
            formula: formula.clone(),
        }),
    }
}

impl std::fmt::Display for Sequent {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{} -> {}", self.body_formula, self.head_formula)
    }
}
