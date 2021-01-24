use super::{
    attribute::{Attribute, AttributeList},
    constants::*,
    expression::Convertor,
    symbol::Symbol,
    Error, Tuple,
};
use crate::chase::SequentTrait;
use codd::expression as rel_exp;
use itertools::Itertools;
use razor_fol::{
    syntax::{formula::Atomic, Const, Func, Pred, Var, FOF},
    transform::{Relational, ToRelational, GNF},
};
use std::convert::TryFrom;

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
    body_formula: FOF,

    /// The head of the implication from which the sequent was made.
    head_formula: FOF,
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

    pub(super) fn new(gnf: &GNF, convertor: &mut Convertor) -> Result<Self, Error> {
        // relationalize and expand equalities of `body` and `head`:
        let body_linear = gnf
            .body()
            .relational_with(
                &mut var_generator(),
                &mut const_generator(),
                &mut fn_generator(),
            )
            .linear_with(&mut linear_generator());
        let head_relational = gnf.head().relational_with(
            &mut var_generator(),
            &mut const_generator(),
            &mut fn_generator(),
        );
        let branches = build_branches(&head_relational)?; // relationalized right is enough for building branches
        let head_linear = head_relational.linear_with(&mut linear_generator());

        let head_attributes = AttributeList::try_from(&head_linear)?.universals();
        let range = Vec::from(&head_attributes);

        // apply range restriction:
        let body_range_restricted = body_linear.range_restrict(&range, DOMAIN);
        let head_range_restricted = head_linear.range_restrict(&range, DOMAIN);

        let body_attributes =
            AttributeList::try_from(&body_range_restricted)?.intersect(&head_attributes);

        let body_expression = convertor.convert(&body_range_restricted, &body_attributes)?;
        let head_expression = convertor.convert(&head_range_restricted, &body_attributes)?;

        let expression = match &branches[..] {
            [] => body_expression, // Bottom
            _ => match &branches[0][..] {
                [] => rel_exp::Mono::from(rel_exp::Empty::new()), // Top
                _ => {
                    rel_exp::Mono::from(rel_exp::Difference::new(body_expression, head_expression))
                } // Other
            },
        };

        Ok(Self {
            branches,
            attributes: body_attributes,
            expression,
            body_formula: gnf.body().into(),
            head_formula: gnf.head().into(),
        })
    }
}

impl SequentTrait for Sequent {
    fn body(&self) -> FOF {
        self.body_formula.clone()
    }

    fn head(&self) -> FOF {
        self.head_formula.clone()
    }
}

// functions to generate symbols for relationalization and linearization:
fn var_generator() -> impl FnMut() -> Var {
    let mut var_counter = 0;
    move || {
        let name = format!("{}{}", EXISTENTIAL_PREFIX, var_counter);
        var_counter += 1;
        name.into()
    }
}

fn const_generator() -> impl FnMut(&Const) -> Pred {
    |c: &Const| constant_instance_name(c).into()
}

fn fn_generator() -> impl FnMut(&Func) -> Pred {
    |f: &Func| function_instance_name(f).into()
}

fn linear_generator() -> impl FnMut(&str, u32) -> Var {
    |name: &str, count| format!("{}{}{}{}", EQUATIONAL_PREFIX, name, SEPERATOR, count).into()
}

fn build_branches(rel: &Relational) -> Result<Vec<Vec<Atom>>, Error> {
    let mut branches = Vec::new();
    for clause in rel.iter() {
        let mut new_clause = Vec::new();
        for atomic in clause.iter() {
            match atomic {
                Atomic::Atom(this) => {
                    let predicate = &this.predicate;
                    let terms = &this.terms;

                    // calling `into_canonical` is unnecessary when branches are built
                    // before equality expansion because there are no equational
                    // attributes. (the existing algorithm)
                    let attributes = terms
                        .iter()
                        .map(|v| Attribute::try_from(v.symbol()))
                        .collect::<Result<Vec<_>, _>>()?;

                    let symbol = if predicate.name() == DOMAIN {
                        Symbol::Domain
                    } else if predicate.name().starts_with(CONSTANT_PREDICATE_PREFIX) {
                        Symbol::Const(Const::from(&predicate.name()[1..]))
                    } else if predicate.name().starts_with(FUNCTIONAL_PREDICATE_PREFIX) {
                        Symbol::Func {
                            symbol: Func::from(&predicate.name()[1..]),
                            arity: (terms.len() - 1) as u8,
                        }
                    } else {
                        Symbol::Pred {
                            symbol: Pred::from(predicate.name()),
                            arity: terms.len() as u8,
                        }
                    };

                    new_clause.push(Atom::new(&symbol, AttributeList::new(attributes)));
                }
                Atomic::Equals(this) => {
                    let left = Attribute::try_from(this.left.symbol())?;
                    let right = Attribute::try_from(this.right.symbol())?;

                    new_clause.push(Atom::new(
                        &Symbol::Equality,
                        AttributeList::new(vec![left, right]),
                    ));
                }
            }
        }
        branches.push(new_clause);
    }

    // optimizing the branches:
    let result = if branches.iter().any(|branch| branch.is_empty()) {
        vec![vec![]] // logically the right is true
    } else {
        // Remove duplicate atoms is necessary for correctness:
        branches
            .into_iter()
            .map(|branch| branch.into_iter().unique().collect())
            .collect()
    };

    Ok(result)
}

impl std::fmt::Display for Sequent {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{} -> {}", self.body_formula, self.head_formula)
    }
}
