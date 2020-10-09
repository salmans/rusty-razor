use super::{constants::*, empty_named_tuple, sequent::Sequent, NamedTuple, Symbol, Tuple};
use crate::chase::{r#impl::basic::WitnessTerm, ModelTrait, Observation, E};
use anyhow::Result;
use razor_fol::syntax::Sig;
use relalg::expression as rel_exp;
use std::{collections::HashMap, fmt};

/// Implements an instance of [`ModelTrait`] with an underlying database.
/// It uses [`WitnessTerm`] from the basic implementation to represent observations.
///
/// [`ModelTrait`]: ../../trait.ModelTrait.html
/// [`WitnessTerm`]: ../basic/enum.WitnessTerm.html
#[derive(Clone)]
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
    pub database: relalg::Database,

    /// Maps each symbol to their corresponding relational expression.
    relations: HashMap<Symbol, rel_exp::Relation<Tuple>>,
}

impl Model {
    /// Creates a new model over the given `signature`.
    pub fn new(signature: &Sig) -> Self {
        let mut database = relalg::Database::new();
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
        mut tuples: relalg::Tuples<Tuple>,
    ) -> Result<()> {
        if let Some(relation) = self.relations.get(symbol) {
            let to_add = Vec::new();
            if let Symbol::Equality = symbol {
                let mut to_add = Vec::new();
                for t in tuples.iter() {
                    to_add.push(vec![t[1], t[0]]);
                }
            };
            tuples.extend(to_add);

            self.database
                .insert(relation, tuples)
                .map_err(|_| anyhow::anyhow!("internal error: failed to insert into database"))
        } else {
            anyhow::bail!(format!(
                "internal error: missing relation for symbol: {:#?}",
                symbol
            ))
        }
    }

    pub(super) fn database_mut(&mut self) -> &mut relalg::Database {
        &mut self.database
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
    db: &mut relalg::Database,
) -> Result<HashMap<Symbol, rel_exp::Relation<Tuple>>> {
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
