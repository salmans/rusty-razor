use super::{
    constants::*, empty_named_tuple, equation_rewrite::Rewrite, sequent::Sequent, Error,
    NamedTuple, Symbol, Tuple,
};
use crate::chase::{r#impl::basic::WitnessTerm, ModelTrait, Observation, E};
use codd::expression as rel_exp;
use razor_fol::syntax::Sig;
use std::{collections::HashMap, fmt};

/// Implements an instance of [`ModelTrait`] with an underlying database.
/// It uses [`WitnessTerm`] from the basic implementation to represent observations.
///
/// [`ModelTrait`]: ../../trait.ModelTrait.html
/// [`WitnessTerm`]: ../basic/enum.WitnessTerm.html
pub struct Model {
    /// Is a unique identifier for this model.
    id: u64,

    /// Keeps track of the next index to assign to a new element of this model.
    element_index: i32,

    /// Maps *flat* witness terms to elements of this model.
    ///
    /// **Hint**: Flat (witness) terms are terms that do not contain any composite sub-terms,
    /// consisting of functions applications.
    rewrites: HashMap<WitnessTerm, E>,

    /// Stores the information contained in this model.
    pub database: codd::Database,

    /// Maps each symbol to their corresponding relational expression.
    relations: HashMap<Symbol, rel_exp::Relation<Tuple>>,
}

impl Model {
    /// Creates a new model over the given `signature`.
    pub fn new(signature: &Sig) -> Self {
        let mut database = codd::Database::new();
        let relations = build_relations_info(signature, &mut database)
            .expect("internal error: failed to initialize model");

        Self {
            id: rand::random(),
            element_index: 0,
            rewrites: HashMap::new(),
            database,
            relations,
        }
    }

    /// Creates a new element for the given `witness` and records that `witness`
    /// denotes the new element.
    pub fn new_element(&mut self, witness: WitnessTerm) -> E {
        let element = E(self.element_index);
        self.element_index = self.element_index + 1;
        self.rewrites.insert(witness, element.clone());
        element
    }

    // assumes that the witness term is flat
    pub(super) fn record(&mut self, witness: WitnessTerm) -> E {
        match witness {
            WitnessTerm::Elem { element } => element,
            WitnessTerm::Const { .. } => {
                if let Some(e) = self.rewrites.get(&witness) {
                    (*e).clone()
                } else {
                    self.new_element(witness)
                }
            }
            WitnessTerm::App { .. } => {
                // The input term is assumed to be flat -- no recursive lookups:
                if let Some(e) = self.rewrites.get(&witness) {
                    (*e).clone()
                } else {
                    self.new_element(witness)
                }
            }
        }
    }

    /// Evaluates a sequent in the model.
    pub(super) fn evaluate<'a>(&self, sequent: &'a Sequent) -> Vec<NamedTuple<'a>> {
        let mut result = Vec::new();

        let tuples = self
            .database
            .evaluate(sequent.expression())
            .expect(&format!(
                "internal error: failed to evaluate sequent: {}",
                sequent
            ));

        for tuple in tuples.into_tuples().into_iter() {
            let mut elements = empty_named_tuple();
            for (i, attr) in sequent.attributes().iter().enumerate() {
                elements.insert(attr, tuple[i]);
            }

            result.push(elements);
        }

        result
    }

    pub(super) fn insert(
        &mut self,
        symbol: &Symbol,
        mut tuples: codd::Tuples<Tuple>,
    ) -> Result<(), Error> {
        if let Some(relation) = self.relations.get(symbol) {
            if let Symbol::Equality = symbol {
                let mut to_add = Vec::new();
                for t in tuples.iter() {
                    to_add.push(vec![t[1], t[0]]);
                }
                tuples.extend(to_add);
            };
            self.database
                .insert(relation, tuples)
                .map_err(|e| Error::from(e))
        } else {
            Err(Error::MissingSymbol {
                symbol: symbol.to_string(),
            })
        }
    }

    /// Returns a mutable reference to the underlying database of this model.
    pub(super) fn database_mut(&mut self) -> &mut codd::Database {
        &mut self.database
    }

    fn equation_rewrites(&self) -> Result<Rewrite<E>, Error> {
        let mut rewrite = Rewrite::new();
        let eq_relation = self
            .relations
            .get(&Symbol::Equality)
            .ok_or(Error::MissingSymbol {
                symbol: EQUALITY.into(),
            })?;
        let equations = self.database.evaluate(&eq_relation)?;
        for eq in equations.iter() {
            let l = eq.get(0).unwrap();
            let r = eq.get(1).unwrap();
            rewrite.add(l, r)
        }

        Ok(rewrite)
    }

    fn rewrite_model(&mut self, rewrite: &Rewrite<E>) {
        let mut conversion_map = HashMap::new();
        let mut count = 0;
        for item in rewrite.canonicals() {
            conversion_map.insert(item, E(count));
            count += 1;
        }

        let domain = self.domain();
        for element in domain.iter() {
            let canonical = rewrite.canonical(element).unwrap();
            if conversion_map.contains_key(element) {
                continue;
            }
            let convert = conversion_map
                .get(rewrite.canonical(canonical).unwrap())
                .unwrap()
                .clone();

            conversion_map.insert(element, convert);
        }

        let mut rewrites = HashMap::new();
        for (term, element) in &self.rewrites {
            let new_term = match &term {
                WitnessTerm::Elem { element } => WitnessTerm::Elem {
                    element: conversion_map.get(element).unwrap().clone(),
                },
                WitnessTerm::Const { .. } => term.clone(),
                WitnessTerm::App { function, terms } => WitnessTerm::App {
                    function: function.clone(),
                    terms: terms
                        .iter()
                        .map(|e| {
                            let e = match e {
                                WitnessTerm::Elem { element } => element,
                                _ => unreachable!(),
                            };
                            WitnessTerm::Elem {
                                element: conversion_map.get(e).unwrap().clone(),
                            }
                        })
                        .collect(),
                },
            };

            let new_element = conversion_map.get(&element).unwrap().clone();
            rewrites.insert(new_term, new_element);
        }

        let mut database = codd::Database::new();
        use itertools::Itertools;

        for relation in self.relations.values() {
            let new_relation = database.add_relation(relation.name()).unwrap();
            let tuples = self.database.evaluate(relation).unwrap();
            let new_tuples: codd::Tuples<_> = tuples
                .into_tuples()
                .into_iter()
                .map(|tuple| {
                    tuple
                        .into_iter()
                        .map(|e| conversion_map.get(&e).unwrap().clone())
                        .collect_vec()
                })
                .collect_vec()
                .into();

            database.insert(&new_relation, new_tuples).unwrap();
        }

        self.rewrites = rewrites;
        self.database = database;
    }
}

impl ModelTrait for Model {
    type TermType = WitnessTerm;

    fn get_id(&self) -> u64 {
        self.id
    }

    fn domain(&self) -> Vec<E> {
        self.database
            .evaluate(self.relations.get(&Symbol::Domain).unwrap())
            .expect("internal error: failed to read domain elements")
            .iter()
            .map(|e| e[0].clone())
            .collect()
    }

    fn facts(&self) -> Vec<Observation<Self::TermType>> {
        let mut result = Vec::new();
        for (symbol, relation) in &self.relations {
            match symbol {
                Symbol::Const { .. }
                | Symbol::Func { .. }
                | Symbol::Pred { .. }
                | Symbol::Equality => {
                    let observations = Vec::new();
                    let tuples = self.database.evaluate(relation).unwrap();

                    for t in tuples.into_tuples() {
                        result.push(symbol.observation(&t).unwrap());
                    }
                    result.extend(observations);
                }
                Symbol::Domain => {}
            }
        }

        result
    }

    fn witness(&self, element: &E) -> Vec<WitnessTerm> {
        self.rewrites
            .iter()
            .filter(|(_, e)| *e == element)
            .map(|(t, _)| t)
            .cloned()
            .collect()
    }

    fn element(&self, witness: &WitnessTerm) -> Option<E> {
        match witness {
            WitnessTerm::Elem { element } => self.domain().into_iter().find(|e| e == element),
            WitnessTerm::Const { .. } => self.rewrites.get(witness).cloned(),
            WitnessTerm::App { function, terms } => {
                let terms: Vec<Option<E>> = terms.iter().map(|t| self.element(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    None
                } else {
                    let terms: Vec<WitnessTerm> = terms
                        .into_iter()
                        .map(|e| e.unwrap().clone().into())
                        .collect();
                    self.rewrites
                        .get(&WitnessTerm::App {
                            function: (*function).clone(),
                            terms,
                        })
                        .cloned()
                }
            }
        }
    }

    fn finalize(mut self) -> Self {
        let rewrites = self.equation_rewrites().unwrap();
        self.rewrite_model(&rewrites);
        self
    }
}

impl Clone for Model {
    fn clone(&self) -> Self {
        Self {
            id: rand::random(),
            element_index: self.element_index,
            rewrites: self.rewrites.clone(),
            database: self.database.clone(),
            relations: self.relations.clone(),
        }
    }
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use itertools::Itertools;

        let domain: Vec<String> = self.domain().into_iter().map(|e| e.to_string()).collect();
        let elements: Vec<String> = self
            .domain()
            .iter()
            .sorted()
            .iter()
            .map(|e| {
                let witnesses: Vec<String> =
                    self.witness(e).iter().map(|w| w.to_string()).collect();
                let witnesses = witnesses.into_iter().sorted();
                format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e)
            })
            .collect();
        let facts: Vec<String> = self.facts().into_iter().map(|e| e.to_string()).collect();
        write!(
            f,
            "Domain: {{{}}}\nElements:{}\nFacts: {}\n",
            domain.join(", "),
            elements.join(", "),
            facts.join(", ")
        )
    }
}

// Creates a dictionary of signatures and their corresponding relations to
// access their instances in the database.
fn build_relations_info(
    sig: &Sig,
    db: &mut codd::Database,
) -> Result<HashMap<Symbol, rel_exp::Relation<Tuple>>, Error> {
    let mut relations = HashMap::new();
    for c in sig.constants().iter() {
        let name = constant_instance_name(c);
        let relation = db.add_relation::<Tuple>(&name)?;

        relations.insert(Symbol::Const(c.clone()), relation);
    }
    for f in sig.functions().values() {
        let name = function_instance_name(&f.symbol);
        let relation = db.add_relation::<Tuple>(&name)?;

        relations.insert(
            Symbol::Func {
                symbol: f.symbol.clone(),
                arity: f.arity,
            },
            relation,
        );
    }
    for p in sig.predicates().values() {
        if p.symbol.0 == EQUALITY {
            // Equality is a special case (below)
            continue;
        }
        let name = predicate_instance_name(&p.symbol);
        let relation = db.add_relation::<Tuple>(&name)?;

        relations.insert(
            Symbol::Pred {
                symbol: p.symbol.clone(),
                arity: p.arity,
            },
            relation,
        );
    }
    relations.insert(Symbol::Domain, db.add_relation::<Tuple>(DOMAIN)?);
    if !relations.contains_key(&Symbol::Equality) {
        relations.insert(Symbol::Equality, db.add_relation::<Tuple>(EQUALITY)?);
    }

    Ok(relations)
}
