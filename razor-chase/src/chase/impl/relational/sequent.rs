use super::{
    attribute::{Attribute, AttributeList},
    constants::*,
    expression::make_expression,
    memo::ViewMemo,
    Symbol, Tuple,
};
use crate::chase::SequentTrait;
use anyhow::{bail, Result};
use codd::expression as rel_exp;
use razor_fol::{
    syntax::{Formula, Pred, Term, C, F, V},
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

    pub(super) fn new(formula: &Formula, memo: Option<&mut ViewMemo>) -> Self {
        use itertools::Itertools;

        if let Formula::Implies { left, right } = formula {
            let right_universals: AttributeList = AttributeList::try_from_formula(right)
                .expect(&format!(
                    "internal error: failed to compute attributes for formula: {}",
                    right
                ))
                .universals();

            let range: Vec<V> = (&right_universals).into();

            let rr_left = relationalize::range_restrict(left, &range, DOMAIN).expect(&format!(
                "internal error: failed to apply range restriction on formula: {}",
                left
            ));
            let rr_right = relationalize::range_restrict(right, &range, DOMAIN).expect(&format!(
                "internal error: failed to apply range restriction on formula: {}",
                right
            ));

            let left_attrs = AttributeList::try_from_formula(&rr_left)
                .expect(&format!(
                    "internal error: failed to compute attributes for formula: {}",
                    rr_left
                ))
                .intersect(&right_universals);

            // Removing duplicate atoms is necessary for correctness:
            let branches: Vec<Branch> = build_branches(&rr_right)
                .expect("internal error: failed to process sequent")
                .into_iter()
                .map(|branch| branch.into_iter().unique().collect())
                .collect();

            // Is it a sequent with `true` in the head:
            let branches = if branches.iter().any(|branch| branch.is_empty()) {
                vec![vec![]]
            } else {
                branches
            };

            let (left_expr, right_expr) = if let Some(memo) = memo {
                (
                    memo.make_expression(&rr_left, &left_attrs),
                    memo.make_expression(&rr_right, &left_attrs),
                )
            } else {
                (
                    make_expression(&rr_left, &left_attrs),
                    make_expression(&rr_right, &left_attrs),
                )
            };

            let left_expression = left_expr.expect(&format!(
                "internal error: failed to compute relational expression for formula: {}",
                rr_left
            ));
            let right_expression = right_expr.expect(&format!(
                "internal error: failed to compute relational expression for formula: {}",
                rr_right
            ));

            let expression = match &branches[..] {
                [] => left_expression,
                _ => match &branches[0][..] {
                    [] => rel_exp::Mono::Empty(rel_exp::Empty::new()),
                    _ => rel_exp::Mono::Difference(rel_exp::Difference::new(
                        left_expression.boxed(),
                        right_expression.boxed(),
                    )),
                },
            };

            Self {
                branches,
                attributes: left_attrs,
                expression,
                body_formula: rr_left.clone(),
                head_formula: rr_right.clone(),
            }
        } else {
            panic!("something is wrong: expecting a geometric sequent in standard form")
        }
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

fn build_branches(formula: &Formula) -> Result<Vec<Vec<Atom>>> {
    use std::convert::TryFrom;

    match formula {
        Formula::Top => Ok(vec![vec![]]),
        Formula::Bottom => Ok(vec![]),
        Formula::Atom { predicate, terms } => {
            let mut attributes = Vec::new();
            for term in terms {
                match term {
                    Term::Var { variable } => attributes.push(
                        Attribute::try_from(variable)
                            .map(Attribute::into_canonical)
                            .expect("internal error: invalid variable name"),
                    ),
                    _ => bail!("something went wrong: expacting a variable"),
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
                bail!("something is wrong: expecting a geometric sequent in standard form.")
            }
        }
        Formula::Or { left, right } => {
            let mut left = build_branches(left)?;
            let mut right = build_branches(right)?;
            left.append(&mut right);
            Ok(left)
        }
        _ => bail!("something is wrong: expecting a geometric sequent in standard form."),
    }
}

impl std::fmt::Display for Sequent {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{} -> {}", self.body_formula, self.head_formula)
    }
}
