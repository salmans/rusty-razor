use super::{
    constants::*, empty_named_tuple, rewrite::Rewrite, sequent::Sequent, symbol::Symbol, Error,
    NamedTuple, Tuple,
};
use crate::chase::{r#impl::basic::WitnessTerm, ModelTrait, Observation, E};
use codd::expression as rel_exp;
use itertools::Itertools;
use razor_fol::syntax::Sig;
use std::{collections::HashMap, fmt};

/// Implements an instance of [`ModelTrait`] with an underlying database.
/// It uses [`WitnessTerm`] from the basic implementation to represent observations.
///
/// [`ModelTrait`]: crate::chase::ModelTrait
/// [`WitnessTerm`]: crate::chase::impl::basic::WitnessTerm
pub struct Model {
    /// Is a unique identifier for this model.
    id: u64,

    /// Keeps track of the next index to assign to a new element of this model.
    element_index: i32,

    /// Maps *flat* witness terms to elements of this model.
    ///
    /// **Hint**: Flat (witness) terms are terms that do not contain any complex sub-terms
    /// that consist of functions applications.
    rewrites: HashMap<WitnessTerm, E>,

    /// Stores the information contained in this model.
    database: codd::Database,

    /// Maps each symbol to their corresponding relational expression.
    relations: HashMap<Symbol, rel_exp::Relation<Tuple>>,
}

impl Model {
    /// Creates a new model over the given `signature`.
    pub fn new(signature: &Sig) -> Self {
        let mut database = codd::Database::new();
        let relations = relations_map(signature, &mut database).unwrap();
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
    fn new_element(&mut self, witness: WitnessTerm) -> E {
        let element = E(self.element_index);
        self.element_index += 1;
        self.rewrites.insert(witness, element);
        element
    }

    // assumes that the witness term is flat
    pub(super) fn record(&mut self, witness: WitnessTerm) -> E {
        match witness {
            WitnessTerm::Elem(e) => e,
            _ => self
                .rewrites
                .get(&witness)
                .copied()
                .unwrap_or_else(|| self.new_element(witness)),
        }
    }

    /// Evaluates a sequent in the model.
    pub(super) fn evaluate<'a>(&self, sequent: &'a Sequent) -> Vec<NamedTuple<'a>> {
        let tuples = self.database.evaluate(sequent.expression()).unwrap();
        tuples
            .into_tuples()
            .into_iter()
            .map(|tuple| {
                let mut elements = empty_named_tuple();
                for (i, attr) in sequent.attributes().iter().enumerate() {
                    elements.insert(attr, tuple[i]);
                }
                elements
            })
            .collect()
    }

    pub(super) fn insert(
        &mut self,
        symbol: &Symbol,
        mut tuples: codd::Tuples<Tuple>,
    ) -> Result<(), Error> {
        if let Some(relation) = self.relations.get(symbol) {
            if let Symbol::Equality = symbol {
                let to_add = tuples.iter().map(|t| vec![t[1], t[0]]).collect_vec();
                tuples.extend(to_add);
            };
            self.database.insert(relation, tuples).map_err(Error::from)
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
            rewrite.rewrite(&eq[0], &eq[1])
        }
        Ok(rewrite)
    }

    fn rewrite_model(&mut self, rewrite: &Rewrite<E>) {
        let mut conversion_map = HashMap::new();
        let normal_forms = rewrite.normal_forms().into_iter().sorted();
        for (count, item) in normal_forms.into_iter().enumerate() {
            conversion_map.insert(item, E(count as i32));
        }

        let domain = self.domain();
        for element in domain.iter() {
            let canonical = rewrite.normalize(element).unwrap();
            if conversion_map.contains_key(element) {
                continue;
            }
            let convert = *conversion_map
                .get(rewrite.normalize(canonical).unwrap())
                .unwrap();

            conversion_map.insert(element, convert);
        }

        let mut rewrites = HashMap::new();
        for (term, element) in &self.rewrites {
            let new_term = match &term {
                WitnessTerm::Elem(e) => WitnessTerm::Elem(*conversion_map.get(e).unwrap()),
                WitnessTerm::Const(_) => term.clone(),
                WitnessTerm::App { function, terms } => WitnessTerm::App {
                    function: function.clone(),
                    terms: terms
                        .iter()
                        .map(|e| {
                            let e = match e {
                                WitnessTerm::Elem(e) => e,
                                _ => unreachable!(),
                            };
                            WitnessTerm::Elem(*conversion_map.get(e).unwrap())
                        })
                        .collect(),
                },
            };

            let new_element = *conversion_map.get(element).unwrap();
            rewrites.insert(new_term, new_element);
        }

        let mut database = codd::Database::new();
        for relation in self.relations.values() {
            let new_relation = database.add_relation(relation.name()).unwrap();
            let tuples = self.database.evaluate(relation).unwrap();
            let new_tuples: codd::Tuples<_> = tuples
                .into_tuples()
                .into_iter()
                .map(|tuple| {
                    tuple
                        .into_iter()
                        .map(|e| *conversion_map.get(&e).unwrap())
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
            .unwrap()
            .iter()
            .map(|e| e[0])
            .collect()
    }

    fn facts(&self) -> Vec<Observation<Self::TermType>> {
        let mut result = Vec::new();
        for (symbol, relation) in &self.relations {
            match symbol {
                Symbol::Domain | Symbol::Equality => {}
                _ => {
                    let observations = Vec::new();
                    let tuples = self.database.evaluate(relation).unwrap();

                    for t in tuples.into_tuples() {
                        result.push(symbol.observation(&t).unwrap());
                    }
                    result.extend(observations);
                }
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
            WitnessTerm::Elem(element) => self.domain().into_iter().find(|e| e == element),
            WitnessTerm::Const(_) => self.rewrites.get(witness).cloned(),
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

impl fmt::Debug for Model {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
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
fn relations_map(
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
        if p.symbol.name() == EQUALITY {
            continue; // Equality is a special case (below)
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
    relations
        .entry(Symbol::Equality)
        .or_insert(db.add_relation::<Tuple>(EQUALITY)?);

    Ok(relations)
}
