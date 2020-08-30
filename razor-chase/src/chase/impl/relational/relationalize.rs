use anyhow::{bail, Result};
use razor_fol::syntax::{Formula, Pred, Term, EQ_SYM, V};
use std::collections::HashMap;

// creates a prefixed variable for relationalization.
macro_rules! prefixed_var {
    ($v:expr) => {
        V(format!("?{}", $v))
    };
}

// creates a functional predicate for relationalization.
#[macro_export]
macro_rules! func_pred {
    ($f:expr) => {
        Pred(format!("${}", $f))
    };
}

// creates a functional predicate for relationalization.
macro_rules! eq_pred {
    () => {
        Pred(EQ_SYM.to_string())
    };
}

// creates a variable sufffixed by the given index for equality expansion.
macro_rules! suffixed_var {
    ($v:expr, $i:ident) => {
        V(format!("${}!{}", $v, $i))
    };
}

macro_rules! domain {
    () => {
        Pred("$$domain".to_string())
    };
}

fn relationalize_term(term: &Term, next_index: &mut u32) -> Option<Formula> {
    match term {
        Term::Var { .. } => None,
        Term::Const { constant } => {
            Some(func_pred!(constant).app(vec![prefixed_var!(next_index).into()]))
        }
        Term::App { function, terms } => {
            let mut conjuncts = vec![];
            let mut new_terms = terms
                .iter()
                .map(|t| {
                    if let Some(fmla) = relationalize_term(t, next_index) {
                        let index = *next_index;
                        *next_index = index + 1;
                        conjuncts.push(fmla);
                        prefixed_var!(index).into()
                    } else {
                        t.clone()
                    }
                })
                .collect::<Vec<Term>>();

            new_terms.push(prefixed_var!(next_index).into());

            let fmla = func_pred!(function).app(new_terms);
            if !conjuncts.is_empty() {
                let mut iter = conjuncts.into_iter();
                let first = iter.next().unwrap();
                let conjuncts = iter.fold(first, |f1, f2| f1.and(f2));
                Some(conjuncts.and(fmla))
            } else {
                Some(fmla)
            }
        }
    }
}

// Assumes that the input are the formulae in the head or body of GNF; that is:
// 1. No universal quantifiers
// 2. No existential quantifiers
// 3. Conjuncts are either & or |
fn relationalize_formula(formula: &Formula, next_index: &mut u32) -> Result<Formula> {
    match formula {
        Formula::Top | Formula::Bottom => Ok(formula.clone()),
        Formula::Atom { predicate, terms } => {
            let mut conjuncts = vec![];
            let new_terms = terms
                .iter()
                .map(|t| {
                    if let Some(fmla) = relationalize_term(t, next_index) {
                        let index = *next_index;
                        *next_index = index + 1;
                        conjuncts.push(fmla);
                        prefixed_var!(index).into()
                    } else {
                        t.clone()
                    }
                })
                .collect::<Vec<Term>>();

            let fmla = predicate.clone().app(new_terms);
            if !conjuncts.is_empty() {
                let mut iter = conjuncts.into_iter();
                let first = iter.next().unwrap();
                let conjuncts = iter.fold(first, |f1, f2| f1.and(f2));
                Ok(conjuncts.and(fmla))
            } else {
                Ok(fmla)
            }
        }
        Formula::Equals { left, right } => relationalize_formula(
            &eq_pred!().app(vec![left.clone(), right.clone()]),
            next_index,
        ),
        Formula::And { left, right } => {
            let left = relationalize_formula(left, next_index)?;
            let right = relationalize_formula(right, next_index)?;
            Ok(left.and(right))
        }
        Formula::Or { left, right } => {
            let left = relationalize_formula(left, next_index)?;
            let right = relationalize_formula(right, next_index)?;
            Ok(left.or(right))
        }
        _ => bail!("something went wrong: expecting a geometric sequent in standard form"),
    }
}

// Assumes that the input is a relationalized formulae:
// 1. the conjuncts are `And` and `Or`
// 2. the terms are only variables
fn expand_equality(formula: &Formula, vars: &mut HashMap<V, i32>) -> Result<Formula> {
    match formula {
        Formula::Top | Formula::Bottom => Ok(formula.clone()),
        Formula::Atom { predicate, terms } => {
            let mut equations = Vec::new();
            let mut new_terms = Vec::new();
            for term in terms {
                match term {
                    Term::Var { variable } => {
                        vars.entry(variable.clone())
                            .and_modify(|count| {
                                let new_var = Term::Var {
                                    variable: suffixed_var!(variable, count),
                                };
                                equations.push(eq_pred!().app(vec![
                                    Term::Var {
                                        variable: variable.clone(),
                                    },
                                    new_var.clone(),
                                ]));
                                new_terms.push(new_var);
                                *count += 1;
                            })
                            .or_insert_with(|| {
                                new_terms.push(Term::Var {
                                    variable: variable.clone(),
                                });
                                0
                            });
                    }
                    _ => bail!("something went wrong: expacting a variable"),
                }
            }
            Ok(equations
                .into_iter()
                .fold(predicate.clone().app(new_terms), |fmla, eq| Formula::And {
                    left: Box::new(fmla),
                    right: Box::new(eq),
                }))
        }
        Formula::And { left, right } => {
            let left = expand_equality(left, vars)?;
            let right = expand_equality(right, vars)?;
            Ok(Formula::And {
                left: Box::new(left),
                right: Box::new(right),
            })
        }
        Formula::Or { left, right } => {
            let left = expand_equality(left, vars)?;
            let right = expand_equality(right, vars)?;
            Ok(Formula::Or {
                left: Box::new(left),
                right: Box::new(right),
            })
        }
        _ => bail!("something went wrong: expecting a relational formula"),
    }
}

#[allow(unused)]
// assuming a relationalized existential formula
pub(crate) fn range_restrict(formula: &Formula, range: &[V]) -> Result<Formula> {
    let formula = match formula {
        Formula::Bottom => formula.clone(),
        Formula::Top => {
            if let Some(conjunct) = domain_conjunct(range) {
                conjunct
            } else {
                formula.clone()
            }
        }
        Formula::Atom { .. } | Formula::And { .. } => {
            let free = formula.free_vars();
            let mut range = Vec::from(range);
            range.retain(|x| !free.contains(&x));
            if let Some(conjunct) = domain_conjunct(&range) {
                Formula::And {
                    left: Box::new(formula.clone()),
                    right: Box::new(conjunct),
                }
            } else {
                formula.clone()
            }
        }
        Formula::Or { left, right } => Formula::Or {
            left: Box::new(range_restrict(left, range)?),
            right: Box::new(range_restrict(right, range)?),
        },
        _ => bail!("something went wrong: expecting a relationalized existential formula"),
    };
    Ok(formula)
}

fn domain_conjunct(range: &[V]) -> Option<Formula> {
    if range.is_empty() {
        return None;
    }

    let mut formula = Formula::Atom {
        predicate: domain!(),
        terms: vec![Term::Var {
            variable: range[0].clone(),
        }],
    };

    let mut vs = &range[1..];

    while !vs.is_empty() {
        formula = Formula::And {
            left: Box::new(formula),
            right: Box::new(Formula::Atom {
                predicate: domain!(),
                terms: vec![Term::Var {
                    variable: vs[0].clone(),
                }],
            }),
        };
        vs = &vs[1..];
    }

    Some(formula)
}

#[allow(unused)]
pub(crate) fn relationalize(formula: &Formula) -> Result<Formula> {
    let formula = relationalize_formula(formula, &mut 0)?;
    expand_equality(&formula, &mut HashMap::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use razor_fol::{formula, v};

    #[test]
    fn test_relationalize_formula() -> Result<()> {
        assert_eq! {
            "⊤",
            relationalize_formula(&formula!('|'), &mut 0)?.to_string(),
        };
        assert_eq! {
            "⟘",
            relationalize_formula(&formula!(_|_), &mut 0)?.to_string(),
        };
        assert_eq! {
            "P()",
            relationalize_formula(&formula!(P()), &mut 0)?.to_string(),
        };
        assert_eq! {
            "P(x, y)",
            relationalize_formula(&formula!(P(x, y)), &mut 0)?.to_string(),
        };
        assert_eq! {
            "=(x, y)",
            relationalize_formula(&formula!((x) = (y)), &mut 0)?.to_string(),
        }
        assert_eq! {
            r"$'c(?0) ∧ =(x, ?0)",
            relationalize_formula(&formula!((x) = (@c)), &mut 0)?.to_string(),
        }
        assert_eq! {
            r"($'c(?0) ∧ $'d(?1)) ∧ =(?0, ?1)",
            relationalize_formula(&formula!((@c) = (@d)), &mut 0)?.to_string(),
        }
        assert_eq! {
            r"$'c(?0) ∧ P(?0)",
            relationalize_formula(&formula!(P(@c)), &mut 0)?.to_string(),
        };
        assert_eq! {
            r"$'c(?0) ∧ P(x, ?0)",
            relationalize_formula(&formula!(P(x, @c)), &mut 0)?.to_string(),
        };
        assert_eq! {
            r"($'c(?0) ∧ $'d(?1)) ∧ P(?0, ?1)",
            relationalize_formula(&formula!(P(@c, @d)), &mut 0)?.to_string(),
        };
        assert_eq! {
            r"$f(x, ?0) ∧ P(?0)",
            relationalize_formula(&formula!(P(f(x))), &mut 0)?.to_string(),
        };
        assert_eq! {
            "($g(x, ?0) ∧ $f(?0, ?1)) ∧ P(?1)",
            relationalize_formula(&formula!(P(f(g(x)))), &mut 0)?.to_string(),
        };
        assert_eq! {
            "(($g(x, ?0) ∧ $f(?0, ?1)) ∧ $f(y, ?2)) ∧ P(?1, ?2)",
            relationalize_formula(&formula!(P(f(g(x)), f(y))), &mut 0)?.to_string(),
        };
        assert_eq! {
            "P(x) ∧ Q(y)",
            relationalize_formula(&formula!((P(x)) & (Q(y))), &mut 0)?.to_string(),
        };
        assert_eq! {
            "($\'c(?0) ∧ P(?0)) ∧ ($\'d(?1) ∧ Q(?1))",
            relationalize_formula(&formula!((P(@c)) & (Q(@d))), &mut 0)?.to_string(),
        };
        assert_eq! {
            "P(x) ∨ Q(y)",
            relationalize_formula(&formula!((P(x)) | (Q(y))), &mut 0)?.to_string(),
        };
        assert_eq! {
            "($\'c(?0) ∧ P(?0)) ∨ ($\'d(?1) ∧ Q(?1))",
            relationalize_formula(&formula!((P(@c)) | (Q(@d))), &mut 0)?.to_string(),
        };

        assert!(relationalize_formula(&formula!(~[P()]), &mut 0).is_err());
        assert!(relationalize_formula(&formula!([P()] -> [Q()]), &mut 0).is_err());
        assert!(relationalize_formula(&formula!([P()] <=> [Q()]), &mut 0).is_err());
        assert!(relationalize_formula(&formula!(?x.[P(x)]), &mut 0).is_err());
        assert!(relationalize_formula(&formula!(!x.[P(x)]), &mut 0).is_err());

        Ok(())
    }

    #[test]
    fn test_expand_equality() -> Result<()> {
        assert_eq!(
            "⊤",
            expand_equality(&formula!('|'), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "⟘",
            expand_equality(&formula!(_|_), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "P()",
            expand_equality(&formula!(P()), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "P(x, y)",
            expand_equality(&formula!(P(x, y)), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "P(x, $x!0) ∧ =(x, $x!0)",
            expand_equality(&formula!(P(x, x)), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∧ (Q($x!0) ∧ =(x, $x!0))",
            expand_equality(&formula!([P(x, y)] & [Q(x)]), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∧ ((Q($x!0, $y!0) ∧ =(x, $x!0)) ∧ =(y, $y!0))",
            expand_equality(&formula!([P(x, y)] & [Q(x, y)]), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "P(x) ∧ ((Q(y, $x!0, $y!0) ∧ =(x, $x!0)) ∧ =(y, $y!0))",
            expand_equality(&formula!([P(x)] & [Q(y, x, y)]), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "(P(x) ∧ (Q($x!0) ∧ =(x, $x!0))) ∧ (R($x!1) ∧ =(x, $x!1))",
            expand_equality(
                &formula!({ [P(x)] & [Q(x)] } & { R(x) }),
                &mut HashMap::new()
            )?
            .to_string(),
        );
        assert_eq!(
            "P(x, y) ∨ (Q($x!0) ∧ =(x, $x!0))",
            expand_equality(&formula!([P(x, y)] | [Q(x)]), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∨ ((Q($x!0, $y!0) ∧ =(x, $x!0)) ∧ =(y, $y!0))",
            expand_equality(&formula!([P(x, y)] | [Q(x, y)]), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "P(x) ∨ ((Q(y, $x!0, $y!0) ∧ =(x, $x!0)) ∧ =(y, $y!0))",
            expand_equality(&formula!([P(x)] | [Q(y, x, y)]), &mut HashMap::new())?.to_string(),
        );
        assert_eq!(
            "(P(x) ∨ (Q($x!0) ∧ =(x, $x!0))) ∨ (R($x!1) ∧ =(x, $x!1))",
            expand_equality(
                &formula!({ [P(x)] | [Q(x)] } | { R(x) }),
                &mut HashMap::new()
            )?
            .to_string(),
        );

        assert!(expand_equality(&formula!(P(@c)), &mut HashMap::new()).is_err());
        assert!(expand_equality(&formula!(P(f(x))), &mut HashMap::new()).is_err());
        assert!(expand_equality(&formula!(~[P()]), &mut HashMap::new()).is_err());
        assert!(expand_equality(&formula!([P()] -> [Q()]), &mut HashMap::new()).is_err());
        assert!(expand_equality(&formula!([P()] <=> [Q()]), &mut HashMap::new()).is_err());
        assert!(expand_equality(&formula!(?x.[P(x)]), &mut HashMap::new()).is_err());
        assert!(expand_equality(&formula!(!x.[P(x)]), &mut HashMap::new()).is_err());

        Ok(())
    }

    #[test]
    fn test_range_restrict() -> Result<()> {
        assert_eq!("⊤", range_restrict(&formula!('|'), &vec![])?.to_string());
        assert_eq!(
            "$$domain(x)",
            range_restrict(&formula!('|'), &vec![v!(x)])?.to_string()
        );
        assert_eq!(
            "$$domain(x) ∧ $$domain(y)",
            range_restrict(&formula!('|'), &vec![v!(x), v!(y)])?.to_string()
        );
        assert_eq!("⟘", range_restrict(&formula!(_|_), &vec![])?.to_string());

        assert_eq!(
            "P(x)",
            range_restrict(&formula!(P(x)), &vec![])?.to_string()
        );
        assert_eq!(
            "P(w, x, y) ∧ $$domain(z)",
            range_restrict(&formula!(P(w, x, y)), &vec![v!(x), v!(y), v!(z)])?.to_string()
        );

        assert_eq!(
            "P(x) ∧ Q(y)",
            range_restrict(&formula!([P(x)] & [Q(y)]), &vec![])?.to_string()
        );
        assert_eq!(
            "(P(v, w) ∧ Q(x)) ∧ ($$domain(y) ∧ $$domain(z))",
            range_restrict(
                &formula!([P(v, w)] & [Q(x)]),
                &vec![v!(v), v!(w), v!(x), v!(y), v!(z)]
            )?
            .to_string()
        );

        assert_eq!(
            "P(x) ∨ Q(y)",
            range_restrict(&formula!([P(x)] | [Q(y)]), &vec![])?.to_string()
        );

        Ok(())
    }

    #[test]
    fn test_relationalize() -> Result<()> {
        assert_eq!(
            "$f(y, ?0) ∧ (P(x, $?0!0) ∧ =(?0, $?0!0))",
            relationalize(&formula!(P(x, f(y))))?.to_string()
        );
        assert_eq!(
            "$f(x, ?0) ∧ ((P($x!0, $?0!0) ∧ =(x, $x!0)) ∧ =(?0, $?0!0))",
            relationalize(&formula!(P(x, f(x))))?.to_string()
        );

        Ok(())
    }
}
