use crate::chase::{BounderTrait, EvaluateResult, EvaluatorTrait, StrategyTrait};

use super::{
    empty_named_tuple,
    model::Model,
    sequent::{Branch, Sequent, SymbolicAtom},
    symbol::Symbol,
    Error, NamedTuple, Tuple,
};
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
            return None; // chase step fails
        }

        let mut open = vec![model.clone()];
        let mut bounded = Vec::new();

        for tuple in tuples {
            open = open
                .into_iter()
                .flat_map(|m| {
                    info!(event = crate::trace::EVALUATE, sequent = %sequent, mapping = ?tuple);
                    let (os, bs) = balance(&tuple, sequent.branches(), &m, bounder)
                        .unwrap()
                        .into_models();
                    bounded.extend(bs);
                    os
                })
                .collect();
        }

        Some(EvaluateResult::from((open, bounded)))
    }
}

#[inline(always)]
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

#[inline(always)]
fn balance<B: BounderTrait>(
    tuple: &NamedTuple,
    branches: &[Branch],
    parent: &Model,
    bounder: Option<&B>,
) -> Result<EvaluateResult<Model>, Error> {
    let mut result = EvaluateResult::new();

    for branch in branches.iter() {
        let mut model = parent.clone();
        let mut symbol_tuples = HashMap::<&Symbol, Vec<Tuple>>::new();
        let mut existentials = empty_named_tuple();
        let mut bounded = false;
        for atom in branch {
            let new_tuple = {
                let (t, b) = balance_atom(&mut model, atom, tuple, &mut existentials, bounder)?;
                bounded |= b;
                t
            };
            symbol_tuples
                .entry(atom.symbol())
                .or_insert_with(Vec::new)
                .push(new_tuple);
        }

        for atom in branch {
            let symbol = atom.symbol();
            if let Some(ts) = symbol_tuples.remove(symbol) {
                model.insert(symbol, ts.into()).unwrap();
            }
        }
        model
            .insert(
                &Symbol::Domain,
                existentials.values().map(|x| vec![*x]).into(),
            )
            .unwrap();

        model
            .insert(
                &Symbol::Equality,
                existentials.into_iter().map(|(_, x)| vec![x, x]).into(),
            )
            .unwrap();

        if bounded {
            result.append_bounded_model(model);
        } else {
            result.append_open_model(model);
        }
    }

    Ok(result)
}

#[inline(always)]
fn balance_atom<'t, B: BounderTrait>(
    model: &mut Model,
    atom: &'t SymbolicAtom,
    tuple: &NamedTuple,
    existentials: &mut NamedTuple<'t>,
    bounder: Option<&B>,
) -> Result<(Tuple, bool), Error> {
    let mut new_tuple = Vec::new();
    let mut bounded = false;
    for attr in atom.attributes().iter() {
        if attr.is_existential() {
            let element = if let Some(element) = existentials.get(attr) {
                *element
            } else {
                let witness = atom.symbol().witness(&new_tuple)?;
                let element = model.record(witness);
                existentials.insert(attr, element);
                element
            };
            new_tuple.push(element);
        } else {
            new_tuple.push(*tuple.get(attr).unwrap());
        }
    }

    if let Some(bounder) = bounder {
        if let Some(obs) = atom.symbol().observation(&new_tuple) {
            if bounder.bound(model, &obs) {
                bounded = true;
            }
        }
    }

    Ok((new_tuple, bounded))
}
