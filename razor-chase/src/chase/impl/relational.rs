mod expression;
mod memo;

use crate::chase::{
    r#impl::basic::WitnessTerm, BounderTrait, EvaluateResult, EvaluatorTrait, ModelTrait,
    Observation, PreProcessorEx, Rel, SequentTrait, StrategyTrait, E,
};
use anyhow::{bail, Result};
use expression::{make_expression, Attributes, Tuple};
use itertools::{Either, Itertools};
use razor_fol::{
    syntax::{Formula, Sig, Term, C, F, V},
    transform::relationalize,
};
use relalg::expression::{Difference, Empty, Mono, Relation};
use std::{collections::HashMap, fmt};

const DOMAIN: &str = "$$domain";

#[allow(unused)]
#[derive(Clone)]
pub struct Model {
    id: u64,
    element_index: i32,
    signature: Sig,
    rewrites: HashMap<WitnessTerm, E>,
    database: relalg::Database,
}

impl Model {
    pub fn new(signature: &Sig) -> Self {
        let mut database = relalg::Database::new();
        for c in signature.constants.iter() {
            // FIXME
            database.add_relation::<Tuple>(&format!("${}", c)).unwrap();
        }
        for f in signature.functions.values() {
            // FIXME
            database
                .add_relation::<Tuple>(&format!("${}", f.symbol))
                .unwrap();
        }
        for p in signature.predicates.values() {
            // FIXME
            database.add_relation::<Tuple>(&p.symbol.0).unwrap();
        }
        database.add_relation::<Tuple>("$$domain").unwrap(); // FIXME
        let _ = database.add_relation::<Tuple>("="); // FIXME

        Self {
            id: rand::random(),
            element_index: 0,
            signature: signature.clone(),
            rewrites: HashMap::new(),
            database,
        }
    }

    fn new_element(&mut self) -> E {
        let element = E(self.element_index);
        self.element_index = self.element_index + 1;
        element
    }
}

impl ModelTrait for Model {
    type TermType = WitnessTerm;

    fn get_id(&self) -> u64 {
        self.id
    }

    fn domain(&self) -> Vec<E> {
        self.database
            .evaluate::<Tuple, _>(&Relation::new("$$domain"))
            .unwrap()
            .iter()
            .map(|e| e[0].clone())
            .collect()
    }

    fn facts(&self) -> Vec<Observation<Self::TermType>> {
        let mut result = Vec::<Observation<WitnessTerm>>::new();
        for p in self.signature.predicates.values() {
            if p.symbol.0 == "$$domain" || p.symbol.0 == "=" {
                continue;
            }
            let tuples = self
                .database
                .evaluate(&Relation::<Tuple>::new(&p.symbol.0))
                .unwrap(); // FIXME

            for t in tuples.items.into_iter() {
                result.push(Observation::Fact {
                    relation: Rel(p.symbol.0.to_string()),
                    terms: t
                        .into_iter()
                        .map(|e| WitnessTerm::Elem { element: e })
                        .collect(),
                });
            }
        }
        for f in self.signature.functions.values() {
            let tuples = self
                .database
                .evaluate(&Relation::<Tuple>::new(&format!("${}", f.symbol)))
                .unwrap();

            for mut t in tuples.items.into_iter() {
                let last = t.remove(f.arity as usize - 1);
                result.push(Observation::Identity {
                    left: WitnessTerm::App {
                        function: f.symbol.clone(),
                        terms: t
                            .into_iter()
                            .map(|e| WitnessTerm::Elem { element: e })
                            .collect(),
                    },
                    right: WitnessTerm::Elem { element: last },
                });
            }
        }
        for c in &self.signature.constants {
            let tuples = self
                .database
                .evaluate(&Relation::<Tuple>::new(&format!("${}", c)))
                .unwrap();

            for mut t in tuples.items.into_iter() {
                result.push(Observation::Identity {
                    left: WitnessTerm::Const {
                        constant: c.clone(),
                    },
                    right: WitnessTerm::Elem {
                        element: t.remove(0),
                    },
                });
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
            // FIXME don't use domain()
            WitnessTerm::Elem { element } => self.domain().into_iter().find(|e| e.eq(&element)),
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

type Branch = Vec<RelationAttr>;

// #[derive(Clone)]
//struct Branch(Vec<RelationAttr>);

// impl Branch {

// }

// impl<I: IntoIterator<Item = RelationAttr>> From<I> for Branch {
//     fn from(attributes: I) -> Self {
//         Self(attributes.into_iter().collect())
//     }
// }
#[derive(Clone)]
pub struct Sequent {
    branches: Vec<Branch>,
    attributes: Attributes,
    projected: Attributes,
    expression: Mono<Tuple>,
    body_formula: Formula,
    head_formula: Formula,
}

impl SequentTrait for Sequent {
    fn body(&self) -> Formula {
        self.body_formula.clone()
    }

    fn head(&self) -> Formula {
        self.head_formula.clone()
    }
}

impl From<&Formula> for Sequent {
    // FIXME: ugly code
    fn from(formula: &Formula) -> Self {
        if let Formula::Implies { left, right } = formula {
            let right_free_vars = right.free_vars();
            let right_attrs: Attributes = right_free_vars
                .iter()
                .filter_map(|v| {
                    // This is a hack for now: remove existentially quantified variables
                    if !v.0.starts_with("~") && !v.0.starts_with("?") {
                        Some((*v).clone())
                    } else {
                        None
                    }
                })
                .collect::<Vec<V>>()
                .into();

            let projected: Attributes = right_free_vars
                .iter()
                .filter_map(|v| {
                    if v.0.starts_with("?") {
                        Some((*v).clone())
                    } else {
                        None
                    }
                })
                .collect::<Vec<V>>()
                .into();

            let rr_left = relationalize::range_restrict(left, &right_attrs, DOMAIN).unwrap(); // FIXME
            let rr_right = relationalize::range_restrict(right, &right_attrs, DOMAIN).unwrap(); // FIXME

            let left_attrs: Attributes = rr_left
                .free_vars()
                .into_iter()
                .map(|v| v.clone())
                .collect::<Vec<V>>()
                .into();

            let left_attrs = left_attrs.intersect(&right_attrs);

            let branches: Vec<Branch> = build_branches(&rr_right)
                .unwrap() // FIXME
                .into_iter()
                .map(|branch| branch.into_iter().unique().collect()) // removing duplicate elements is necessary
                .collect();

            let branches = if branches.iter().any(|branch| branch.is_empty()) {
                vec![vec![]]
            } else {
                branches
            };

            let left_expression = make_expression(&rr_left, &left_attrs).unwrap(); // FIXME
            let right_expression = make_expression(&rr_right, &left_attrs).unwrap(); // FIXME

            let expression = match &branches[..] {
                [] => left_expression,
                _ => match &branches[0][..] {
                    [] => Mono::Empty(Empty::new()),
                    _ => Mono::Difference(Difference::new(
                        &Box::new(left_expression),
                        &Box::new(right_expression),
                    )),
                },
            };

            Self {
                branches,
                attributes: left_attrs,
                projected,
                expression,
                body_formula: rr_left.clone(),
                head_formula: rr_right.clone(),
            }
        } else {
            panic!("something is wrong: expecting a geometric sequent in standard form")
        }
    }
}

pub struct PreProcessor;

impl PreProcessor {
    fn equality_axioms() -> Vec<Formula> {
        use razor_fol::formula;

        vec![
            formula!(['|'] -> [(x) = (x)]),
            formula!([(x) = (y)] -> [(y) = (x)]),
            formula!([{(x) = (y)} & {(y) = (z)}] -> [(x) = (z)]),
        ]
    }

    fn consistency_axioms(sig: &Sig) -> Vec<Formula> {
        let mut result = Vec::new();

        for c in &sig.constants {
            let x = Term::from(V("x".to_string()));
            let y = Term::from(V("y".to_string()));
            let c = Term::from(c.clone());

            let left = {
                let c_x = c.clone().equals(x.clone());
                let c_y = c.clone().equals(y.clone());
                c_x.and(c_y) // ('c = x) & ('c = y)
            };
            let right = x.equals(y); // x = y
            result.push(left.implies(right));
        }

        for f in sig.functions.values() {
            let x = Term::from(V("x".to_string()));
            let y = Term::from(V("y".to_string()));

            let left = {
                let xs = (0..f.arity)
                    .map(|n| Term::from(V(format!("x{}", n))))
                    .collect::<Vec<_>>();
                let ys = (0..f.arity)
                    .map(|n| Term::from(V(format!("y{}", n))))
                    .collect::<Vec<_>>();

                let f_xs = f.symbol.clone().app(xs.clone()).equals(x.clone());
                let f_ys = f.symbol.clone().app(ys.clone()).equals(y.clone());

                let xs_ys = xs.into_iter().zip(ys.into_iter()).map(|(x, y)| x.equals(y));

                xs_ys.fold(f_xs.and(f_ys), |fmla, eq| fmla.and(eq))
            };

            let right = x.equals(y); // x = y
            result.push(left.implies(right));
        }

        result
    }
}

impl PreProcessorEx for PreProcessor {
    type Sequent = Sequent;
    type Model = Model;

    fn pre_process(&self, theory: &razor_fol::syntax::Theory) -> (Vec<Self::Sequent>, Self::Model) {
        let mut theory = theory.gnf();
        theory
            .extend(Self::equality_axioms())
            .expect("internal error: failed to add equality axioms");
        theory
            .extend(Self::consistency_axioms(theory.signature()))
            .expect("internal error: failed to add consistency axioms");

        (
            theory
                .formulae()
                .into_iter()
                .map(|f| match f {
                    Formula::Implies { left, right } => {
                        let left = relationalize::Relationalizer::new()
                            .relationalize(&left)
                            .expect(&format!("failed to relationalize formula: {}", left));
                        let right = relationalize::Relationalizer::new()
                            .relationalize(&right)
                            .expect(&format!("failed to relationalize formula: {}", right));
                        Sequent::from(&Formula::implies(left, right))
                    }
                    _ => panic!(""),
                })
                .collect(),
            Model::new(&theory.signature()),
        )
    }
}

pub struct Evaluator;

impl<'s, Stg: StrategyTrait<Item = &'s Sequent>, B: BounderTrait> EvaluatorTrait<'s, Stg, B>
    for Evaluator
{
    type Sequent = Sequent;
    type Model = Model;

    fn evaluate(
        &self,
        model: &Model,
        strategy: &mut Stg,
        bounder: Option<&B>,
    ) -> Option<EvaluateResult<Self::Model>> {
        for sequent in strategy {
            // FIXME get rid of unwrap
            let tuples = model.database.evaluate(&sequent.expression).unwrap();
            if !tuples.is_empty() {
                if sequent.branches.is_empty() {
                    return None;
                } else {
                    let mut models = Vec::new();
                    let mut bounded = false;

                    for tuple in tuples.iter() {
                        let mut elements = HashMap::<&V, E>::new();
                        for i in 0..sequent.attributes.len() {
                            elements.insert(&sequent.attributes[i], tuple[i]);
                        }

                        for branch in &sequent.branches {
                            let mut relation_tuples =
                                HashMap::<(&str, &Attributes), Vec<Tuple>>::new();
                            let mut existentials = HashMap::<&V, E>::new();
                            let mut new_model = model.clone();

                            for item in branch.iter() {
                                relation_tuples
                                    .insert((&item.relation_name, &item.attributes), Vec::new());
                            }

                            for item in branch {
                                let mut new_tuple: Vec<E> = Vec::new();
                                for attr in item.attributes.iter() {
                                    if attr.0.starts_with("?") {
                                        if !existentials.contains_key(attr) {
                                            let new_element = new_model.new_element();
                                            existentials.insert(attr, new_element.clone());
                                            // FIXME: move this after inserting elements
                                            let witness = if item.attributes.len() == 1 {
                                                WitnessTerm::Const {
                                                    constant: C(item.relation_name.to_string()),
                                                } // FIXME: drop $
                                            } else {
                                                WitnessTerm::App {
                                                    function: F(item.relation_name.to_string()), // FIXME: drop $
                                                    terms: new_tuple
                                                        .iter()
                                                        .map(|e| WitnessTerm::Elem {
                                                            element: e.clone(),
                                                        })
                                                        .collect(), // guaranteed to be the last element
                                                }
                                            };

                                            new_model.rewrites.insert(witness, new_element);
                                        }
                                        new_tuple.push(existentials.get(&attr).unwrap().clone());
                                    } else {
                                        new_tuple.push(elements.get(&attr).unwrap().clone());
                                    }
                                }

                                // FIXME
                                if let Some(bounder) = bounder {
                                    if !item.relation_name.starts_with("?") {
                                        let obs = if item.relation_name == "=" {
                                            Observation::Identity {
                                                left: WitnessTerm::Elem {
                                                    element: new_tuple[0].clone(),
                                                },
                                                right: WitnessTerm::Elem {
                                                    element: new_tuple[0].clone(),
                                                },
                                            }
                                        } else {
                                            Observation::Fact {
                                                relation: Rel(item.relation_name.to_string()),
                                                terms: new_tuple
                                                    .iter()
                                                    .map(|e| WitnessTerm::Elem {
                                                        element: e.clone(),
                                                    })
                                                    .collect(),
                                            }
                                        };

                                        if bounder.bound(&new_model, &obs) {
                                            bounded = true;
                                        }
                                    }
                                }

                                relation_tuples
                                    .entry((&item.relation_name, &item.attributes))
                                    .and_modify(|tups| tups.push(new_tuple));
                            }

                            for item in branch {
                                new_model
                                    .database
                                    .insert(
                                        &Relation::new(&item.relation_name),
                                        relation_tuples
                                            .remove(&(&item.relation_name, &item.attributes))
                                            .unwrap()
                                            .into(),
                                    )
                                    .unwrap();
                            }
                            new_model
                                .database
                                .insert::<Tuple>(
                                    &Relation::new("$$domain"),
                                    existentials
                                        .values()
                                        .map(|x| vec![x.clone()])
                                        .collect::<Vec<_>>()
                                        .into(),
                                )
                                .unwrap();

                            if !bounded {
                                models.push(Either::Left(new_model));
                            } else {
                                models.push(Either::Right(new_model));
                            }
                        }
                        // FIXME EvaluationResult looks dumb
                        if !models.is_empty() {
                            return Some(EvaluateResult::from(models));
                        }
                    }
                }
            }
        }
        Some(EvaluateResult::new())
    }
}

#[derive(Hash, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct RelationAttr {
    relation_name: String,
    attributes: Attributes,
}

impl RelationAttr {
    fn new(relation_name: &str, attributes: Attributes) -> Self {
        Self {
            relation_name: relation_name.to_string(),
            attributes,
        }
    }
}

fn build_branches(formula: &Formula) -> Result<Vec<Vec<RelationAttr>>> {
    match formula {
        Formula::Top => Ok(vec![vec![]]),
        Formula::Bottom => Ok(vec![]),
        Formula::Atom { predicate, terms } => {
            let mut attributes = Vec::new();
            for term in terms {
                match term {
                    Term::Var { variable } => {
                        if variable.0.starts_with("~") {
                            // Variables introduced by equality on right can take their value from the original variable.
                            if let Some(end) = variable.0.find(":") {
                                let var_name = variable.0[1..end].to_string();
                                attributes.push(V(var_name));
                            } else {
                                bail!("something is wrong: invalid variable name");
                            }
                        } else {
                            attributes.push(variable.clone());
                        }
                    }
                    _ => bail!("something went wrong: expacting a variable"),
                }
            }

            Ok(vec![vec![RelationAttr::new(
                &predicate.0,
                attributes.into(),
            )]])
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
