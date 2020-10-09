use crate::chase::{BounderTrait, EvaluateResult, EvaluatorTrait, StrategyTrait, E};

use super::{
    empty_named_tuple,
    model::Model,
    sequent::{Atom, Branch, Sequent},
    NamedTuple, Symbol, Tuple,
};
use anyhow::Result;
use either::Either;
use std::collections::HashMap;

pub struct Evaluator;

impl<'s, Stg: StrategyTrait<Item = &'s Sequent>, B: BounderTrait> EvaluatorTrait<'s, Stg, B>
    for Evaluator
{
    type Sequent = Sequent;
    type Model = Model;

    fn evaluate(
        &self,
        model: &Self::Model,
        strategy: &mut Stg,
        bounder: Option<&B>,
    ) -> Option<EvaluateResult<Self::Model>> {
        let next_sequent = next_sequent(strategy, model);
        if next_sequent.is_none() {
            return Some(EvaluateResult::new());
        }
        let (sequent, tuples) = next_sequent.unwrap();

        if sequent.branches().is_empty() {
            return None; // failure
        }

        let mut models = Vec::new();

        for branch in sequent.branches() {
            let mut new_model = model.clone();
            if balance_branch(&tuples, branch, &mut new_model, bounder).expect(&format!(
                "internal error: failed to balance branch: {:#?}",
                branch
            )) {
                models.push(Either::Right(new_model))
            } else {
                models.push(Either::Left(new_model))
            }
        }

        // FIXME EvaluationResult looks dumb
        if !models.is_empty() {
            return Some(EvaluateResult::from(models));
        }

        Some(EvaluateResult::new())
    }
}

fn next_sequent<'s, S: StrategyTrait<Item = &'s Sequent>>(
    strategy: &mut S,
    model: &Model,
) -> Option<(&'s Sequent, Vec<NamedTuple<'s>>)> {
    strategy.find_map(|s| {
        let ts = model.evaluate(s);
        if ts.is_empty() {
            None
        } else {
            Some((s, ts))
        }
    })
}

fn balance_branch<B: BounderTrait>(
    tuples: &Vec<NamedTuple>,
    branch: &Branch,
    model: &mut Model,
    bounder: Option<&B>,
) -> Result<bool> {
    let mut relation_tuples = HashMap::<&Atom, Vec<Tuple>>::new();
    let mut existentials = empty_named_tuple();
    let mut bounded = false;

    for tuple in tuples.iter() {
        for atom in branch {
            bounded = balance_atom(
                model,
                atom,
                tuple,
                &mut existentials,
                &mut relation_tuples,
                bounder,
            )?;
        }
    }

    for atom in branch {
        model
            .insert(atom.symbol(), relation_tuples.remove(atom).unwrap().into())
            .unwrap();
    }
    model
        .insert(
            &Symbol::Domain,
            existentials.values().map(|x| vec![x.clone()]).into(),
        )
        .unwrap();

    model
        .insert(
            &Symbol::Equality,
            existentials.into_iter().map(|(_, x)| vec![x, x]).into(),
        )
        .unwrap();

    Ok(bounded)
}

fn balance_atom<'t, B: BounderTrait>(
    model: &mut Model,
    atom: &'t Atom,
    tuple: &NamedTuple,
    existentials: &mut NamedTuple<'t>,
    relation_tuples: &mut HashMap<&'t Atom, Vec<Tuple>>,
    bounder: Option<&B>,
) -> Result<bool> {
    let mut bounded = false;
    let mut new_tuple: Vec<E> = Vec::new();
    for attr in atom.attributes().iter() {
        if attr.is_existential() {
            if !existentials.contains_key(attr) {
                let witness = atom.symbol().witness(&new_tuple)?;
                let new_element = model.new_element(witness);
                existentials.insert(attr, new_element);
            }
            new_tuple.push(existentials.get(attr).unwrap().clone());
        } else {
            new_tuple.push(tuple.get(attr).unwrap().clone());
        }
    }

    if let Some(bounder) = bounder {
        if let Some(obs) = atom.symbol().observation(&new_tuple) {
            if bounder.bound(model, &obs) {
                bounded = true;
            }
        }
    }

    relation_tuples
        .entry(atom)
        .or_insert(Vec::new())
        .push(new_tuple);

    Ok(bounded)
}
