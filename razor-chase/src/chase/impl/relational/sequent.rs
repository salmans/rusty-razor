use super::{
    attribute::{Attribute, AttributeList},
    constants::*,
    expression::Convertor,
    symbol::Symbol,
    Error, Tuple,
};
use crate::chase::Sequent;
use codd::expression as rel_exp;
use itertools::Itertools;
use razor_fol::{
    syntax::{
        formula::{Atom, Atomic, Equals},
        term::Variable,
        Const, Func, Pred, Var, FOF,
    },
    transform::{FlatClause, Relational, ToRelational, GNF},
};
use std::convert::TryFrom;

/// Represents an atomic formula in the head of a `Sequent`.
#[derive(Hash, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct SymbolicAtom {
    /// The relational predicate symbol of the atom.
    symbol: Symbol,

    /// The list of attributes of the atom.
    attributes: AttributeList,
}

impl SymbolicAtom {
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
pub(super) type Branch = Vec<SymbolicAtom>;

/// Represents a sequent for the chase.
#[derive(Clone)]
pub struct RelSequent {
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

impl RelSequent {
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
        let body_linear = optimize_relational(gnf.body())?.linear_with(&mut linear_generator());
        let head_relational = optimize_relational(gnf.head())?;

        // Build sequent (head) branches as it can be done without linearization:
        let branches = build_branches(&head_relational)?;

        let head_linear = head_relational.linear_with(&mut linear_generator());
        let head_attributes = AttributeList::try_from(&head_linear)?.universals();
        let range = Vec::from(&head_attributes);

        // apply range restriction:
        let body_range_restricted = body_linear.range_restrict(&range, DOMAIN);

        // When evaluating the head expression in a database, existential tables can be
        // ignored: any tuple that satisfies the head expression ignoring existential tables
        // can be ignored when extending the database since skolem functions are unique
        // in each sequent anc cannot be filled by other sequents.
        let head_range_restricted = remove_skolem(head_linear).range_restrict(&range, DOMAIN);

        let body_attributes =
            AttributeList::try_from(&body_range_restricted)?.intersect(&head_attributes);

        let body_expression = convertor.convert(&body_range_restricted, &body_attributes)?;
        let head_expression = convertor.convert(&head_range_restricted, &body_attributes)?;

        let expression = if branches.is_empty() {
            body_expression // Failing sequent
        } else if branches[0].is_empty() {
            rel_exp::Mono::from(rel_exp::Empty::new()) // Tautology
        } else {
            rel_exp::Mono::from(rel_exp::Difference::new(body_expression, head_expression))
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

impl Sequent for RelSequent {
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
        let name = existential_variable_name(var_counter);
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
    |name: &str, count| linear_variable_name(name, count).into()
}

fn build_branches(rel: &Relational) -> Result<Vec<Vec<SymbolicAtom>>, Error> {
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

                    new_clause.push(SymbolicAtom::new(&symbol, AttributeList::new(attributes)));
                }
                Atomic::Equals(this) => {
                    let left = Attribute::try_from(this.left.symbol())?;
                    let right = Attribute::try_from(this.right.symbol())?;

                    new_clause.push(SymbolicAtom::new(
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

// Applies a number of transformations on a relational formula to optimize processing of sequents.
fn optimize_relational<T: ToRelational>(formula: &T) -> Result<Relational, Error> {
    let relational = formula.relational_with(
        &mut var_generator(),
        &mut const_generator(),
        &mut fn_generator(),
    );
    relational
        .into_iter()
        .map(unique_function_app)
        .map(|clause| clause.map(unique_literals))
        .map(|clause| clause.and_then(topo_sort))
        .collect()
}

// For (flat) literals corresponding to the application of a function on the same terms,
// ensures that their result is syntactically captured by the same term. This would
// eliminate equality reasoning for the outputs of the function applicaiton.
fn unique_function_app(clause: FlatClause) -> Result<FlatClause, Error> {
    use razor_fol::syntax::formula::Formula;
    use std::collections::HashMap;

    // keeping track of arguments and rewritten output variables:
    let mut term_map = HashMap::<Atom<_>, Variable>::new();
    let mut var_map = HashMap::new();

    for lit in clause.iter() {
        if let Atomic::Atom(atom) = lit {
            if is_function_predicate(&atom.predicate.name()) {
                let (output, terms) = atom
                    .terms
                    .split_last()
                    .ok_or(Error::BadRelationalAtom { atom: atom.clone() })?;
                if is_existential_variable(output.name()) {
                    let key = atom.predicate.clone().app(terms.to_vec());
                    if let Some(value) = term_map.get(&key) {
                        var_map.insert(output.symbol().clone(), value.clone());
                    } else {
                        term_map.insert(key, output.clone());
                    }
                }
            }
        }
    }

    Ok(clause.into_iter().map(|a| a.substitute(&var_map)).collect())
}

fn unique_literals(clause: FlatClause) -> FlatClause {
    use std::collections::HashSet;

    let mut result = Vec::new();
    let mut set = HashSet::new();
    clause.into_iter().for_each(|l| {
        if !set.contains(&l) {
            set.insert(l.clone());
            result.push(l);
        }
    });
    result.into()
}

// Topologically sorts the (atomic) literals of a clause such that:
//   1. The existential variables that show up as arguments of a literal are the last argument (output) of
// at least one of the previous literals (the relationalization algorithm in razor_fol already satisfies
// this property).
//   2. Among literals corresponding to relationalized function applications that output the same existential
// variable, those which correspond to skolem functions show up after the others that correspond to the
// original functions in the theory. Unlike skolem functions, original functions of the theory may appear in
// other sequents. This increases the chance of reusing existing elements of a model by the chase when creating
// new elements can be avoided.
fn topo_sort(clause: FlatClause) -> Result<FlatClause, Error> {
    use petgraph::{algo::toposort, stable_graph::StableGraph};
    use std::collections::HashMap;

    let mut graph = StableGraph::<_, ()>::new();
    let mut node_map = HashMap::<&Variable, Vec<_>>::new();
    for lit in clause.iter() {
        let node = graph.add_node(lit);
        match lit {
            Atomic::Atom(atom) => {
                let terms = if is_function_predicate(&atom.predicate.name()) {
                    let (output, terms) = atom
                        .terms
                        .split_last()
                        .ok_or(Error::BadRelationalAtom { atom: atom.clone() })?;
                    if is_existential_variable(output.name()) {
                        node_map.entry(output).or_insert(Vec::new()).push(node);
                    }
                    terms
                } else {
                    atom.terms.as_slice()
                };

                for var in terms.iter() {
                    if is_existential_variable(var.name()) {
                        let nodes = node_map
                            .get(var)
                            .ok_or(Error::BadExistentialVariable { var: var.clone() })?;
                        nodes.iter().for_each(|n| {
                            graph.add_edge(*n, node, ());
                        });
                    }
                }
            }
            Atomic::Equals(Equals { left, right }) => {
                if is_existential_variable(left.name()) {
                    let nodes = node_map
                        .get(left)
                        .ok_or(Error::BadExistentialVariable { var: left.clone() })?;
                    nodes.iter().for_each(|n| {
                        graph.add_edge(*n, node, ());
                    });
                }
                if is_existential_variable(right.name()) {
                    let nodes = node_map
                        .get(right)
                        .ok_or(Error::BadExistentialVariable { var: right.clone() })?;
                    nodes.iter().for_each(|n| {
                        graph.add_edge(*n, node, ());
                    });
                }
            }
        }
    }

    Ok(toposort(&graph, None)
        .unwrap()
        .into_iter()
        .map(|i| graph.remove_node(i).unwrap().clone())
        .collect())
}

fn remove_skolem(rel: Relational) -> Relational {
    rel.into_iter().map(clause_remove_skolem).collect()
}

fn clause_remove_skolem(clause: FlatClause) -> FlatClause {
    clause
        .into_iter()
        .filter(|item| {
            if let Atomic::Atom(atom) = item {
                !is_skolem_predicate(&atom.predicate.name())
            } else {
                true
            }
        })
        .collect()
}

impl std::fmt::Display for RelSequent {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{} -> {}", self.body_formula, self.head_formula)
    }
}
