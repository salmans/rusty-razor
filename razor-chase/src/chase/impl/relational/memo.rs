use super::{
    attribute::AttributeList,
    expression::{and_expression, atomic_expression, or_expression, RawExpression, SubExpression},
    Tuple,
};
use anyhow::{bail, Result};
use codd::expression::*;
use razor_fol::syntax::Formula;
use std::collections::HashMap;

pub(super) struct ViewMemo<'a> {
    views: HashMap<RawExpression, Mono<Tuple>>,
    database: &'a mut codd::Database,
}

impl<'a> ViewMemo<'a> {
    pub fn new(database: &'a mut codd::Database) -> Self {
        Self {
            views: HashMap::new(),
            database,
        }
    }

    pub fn make_expression(
        &mut self,
        formula: &Formula,
        attributes: &AttributeList,
    ) -> Result<Mono<Tuple>> {
        self.expression(formula, &Vec::new().into(), attributes)
            .map(SubExpression::into_expression)
    }

    fn expression(
        &mut self,
        formula: &Formula,
        join_attr: &AttributeList,
        final_attr: &AttributeList,
    ) -> Result<SubExpression> {
        match formula {
            Formula::Bottom => Ok(SubExpression::new(
                Vec::new().into(),
                |t: &Tuple| t.clone(),
                Mono::Empty(Empty::new()),
                RawExpression::Empty,
            )),
            Formula::Top => Ok(SubExpression::new(
                Vec::new().into(),
                |t: &Tuple| t.clone(),
                Mono::Singleton(Singleton(vec![].into())),
                RawExpression::Full,
            )),
            Formula::Atom {
                predicate,
                terms: _,
            } => {
                let free_vars = formula.free_vars().into_iter().cloned().collect();
                let sub = atomic_expression(predicate, &free_vars, &join_attr, &final_attr);
                let new_sub = if let Ok(mut s) = sub {
                    match s.raw() {
                        RawExpression::Project { .. } => {
                            if !self.views.contains_key(s.raw()) {
                                let expr = s.expression();
                                let view =
                                    self.database.store_view(&Box::new(expr.clone())).unwrap(); // FIXME

                                s.set_expression(Mono::View(view));
                            }
                            Ok(s)
                        }
                        _ => Ok(s),
                    }
                } else {
                    sub
                };
                new_sub
            }
            Formula::And { left, right } => {
                let sub = and_expression(left, right, join_attr, final_attr); //
                if let Ok(mut s) = sub {
                    if !self.views.contains_key(s.raw()) {
                        let expr = s.expression();
                        let view = self.database.store_view(&Box::new(expr.clone())).unwrap(); // FIXME
                        s.set_expression(Mono::View(view));
                    }
                    Ok(s)
                } else {
                    sub
                }
            }

            Formula::Or { left, right } => or_expression(left, right, join_attr, final_attr),
            _ => bail!("expecting a relational formula"),
        }
    }
}
