/*! Implements a relationalization algorithm for formulae.*/

use super::Error;
use crate::syntax::{symbol::Generator, Formula, Pred, Term, V};
use std::collections::HashMap;

/// Provides the relationalization algorithm through its [`relationalize`] method.
///
/// [`relationalize`]: ./struct.Relationalizer.html#method.relationalize
pub struct Relationalizer {
    // Is the symbol used to convert equality to a predicate.
    equality_symbol: String,

    // Is the [`Generator`] instance used to generate variable names used as placeholders
    // in flattened formulae.
    flattening_generator: Generator,

    // Is the [`Generator`] instance used to generate new variable names when variables
    // appear in more than one position.
    equality_generator: Generator,

    // Is the [`Generator`] instance used to create predicate symbols for functions.
    function_predicate_generator: Generator,

    // Is the [`Generator`] instance used to create predicate symbols for constants.
    constant_predicate_generator: Generator,
}

impl Relationalizer {
    /// Creates a new `Relationalizer` instance with default generators and symbols:
    ///   * The equality symbol is `=`.
    ///   * Variables introduced by flattening are prefixed with `?`.
    ///   * Variables appearing in more than one position are distinguished with `~` as the
    /// prefix, followed by `:` and a unique index.
    ///   * Function predicates are prefixed with `$`.
    pub fn new() -> Self {
        Self {
            equality_symbol: "=".into(),
            flattening_generator: Generator::new().set_prefix("?"),
            equality_generator: Generator::new().set_prefix("~").set_delimiter(":"),
            function_predicate_generator: Generator::new().set_prefix("$"),
            constant_predicate_generator: Generator::new().set_prefix("@"),
        }
    }

    /// Use `symbol` for equality predicates.
    pub fn set_equality_symbol<S: Into<String>>(&mut self, symbol: S) {
        self.equality_symbol = symbol.into();
    }

    /// Use `generator` to generate flattening variable names.
    pub fn set_flattening_generator(&mut self, generator: Generator) {
        self.flattening_generator = generator;
    }

    /// Use `generator` to distinguish variables that appear in more than one positions.
    pub fn set_equality_generator(&mut self, generator: Generator) {
        self.equality_generator = generator;
    }

    /// Use `generator` to create function predicate names.
    pub fn set_predicate_generator(&mut self, generator: Generator) {
        self.function_predicate_generator = generator;
    }

    /// Applies the relationalization algorithm on `formula` and returns the relationalized formula
    /// if it succeeds. The underlying algorithm assumes that the input is negation and quantifier-free;
    /// that is, `¬`, `→`, `⇔`, `∃`, `∀` are not allowed as connectives. Relationalization consists of
    /// applying the following rewrites on the input formula:
    ///   * A constant `'c` is replaced by a predicate `C(x)`.
    ///   * A complex term `f(x_1, ..., x_n)` is replaced by a fresh variable `v` and an atomic
    /// formula `F(x_1, ..., x_n, v)` is conjoined with the input formula.
    ///   * A varialbe `v` that appears in more than one position is replaced by a fresh variable
    /// `y` and an equation `v = y` is conjoined with the input formula.
    ///   * An equation `v = y` is replaced with an atomic formula `=(x, y)`.
    ///
    /// **Note**:
    /// The resulting formula is semantically isomorphic to the input *only* in presence of equality and
    /// function integrity axioms in the theory.
    ///
    /// **Note**:
    /// In the resulting formula, the new (placeholder) variables are sorted topologically from left to write
    /// where the ordering relation is the dependency between the new variables.
    /// A varialbe `v` depends on a variable `y` if for a new function predicate, namely `F`,
    /// `F(..., y,..., v)` is a conjunct in the formula (that is, the result of the function replaced by `F`
    /// depends on `y`).
    ///
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::relationalize::Relationalizer;
    ///
    /// let fmla = "P(f(x)) & Q('c)".parse::<Formula>().unwrap();
    /// let result = Relationalizer::new().relationalize(&fmla).unwrap();
    /// assert_eq!(
    ///     r"($f(x, ?0) ∧ (P(~?0:0) ∧ =(?0, ~?0:0))) ∧ (@c(?1) ∧ (Q(~?1:0) ∧ =(?1, ~?1:0)))",
    ///     result.to_string()
    /// );
    ///
    /// let fmla = "~P(x)".parse::<Formula>().unwrap();
    /// assert!(Relationalizer::new().relationalize(&fmla).is_err());    
    /// ```
    pub fn relationalize(&mut self, formula: &Formula) -> Result<Formula, Error> {
        let formula = self.flatten_formula(formula)?;
        self.expand_equality(&formula, &mut HashMap::new())
    }

    // Applies top level flattening on the input formula.
    fn flatten_formula(&mut self, formula: &Formula) -> Result<Formula, Error> {
        match formula {
            Formula::Top | Formula::Bottom => Ok(formula.clone()),
            Formula::Atom { predicate, terms } => {
                let mut conjuncts = vec![];
                let new_terms = terms
                    .iter()
                    .map(|t| {
                        if let Some((fmla, var)) = self.flatten_term(t) {
                            conjuncts.push(fmla);
                            var.into()
                        } else {
                            t.clone()
                        }
                    })
                    .collect::<Vec<Term>>();

                let fmla = predicate.clone().app(new_terms);
                // Preserving the topological order among variables:
                if !conjuncts.is_empty() {
                    let mut iter = conjuncts.into_iter();
                    let first = iter.next().unwrap();
                    let conjuncts = iter.fold(first, |f1, f2| f1.and(f2));
                    Ok(conjuncts.and(fmla))
                } else {
                    Ok(fmla)
                }
            }
            Formula::Equals { left, right } => self.flatten_formula(
                &Pred(self.equality_symbol.clone()).app(vec![left.clone(), right.clone()]),
            ),
            Formula::And { left, right } => {
                let left = self.flatten_formula(left)?;
                let right = self.flatten_formula(right)?;
                Ok(left.and(right))
            }
            Formula::Or { left, right } => {
                let left = self.flatten_formula(left)?;
                let right = self.flatten_formula(right)?;
                Ok(left.or(right))
            }
            _ => Err(Error::RelationalizeFailure {
                formula: formula.clone(),
            }),
        }
    }

    // Recursively flattens a term and returns the resulting formula together with a placeholder variable
    // for the term. Nothing needs to be done if the input term is a variable.
    fn flatten_term(&mut self, term: &Term) -> Option<(Formula, V)> {
        match term {
            Term::Var { .. } => None,
            Term::Const { constant } => {
                let var = V(self.flattening_generator.next().into());
                let pred = Pred(
                    self.constant_predicate_generator
                        .symbol(constant.0.to_string()),
                );
                let fmla = pred.app(vec![var.clone().into()]);
                Some((fmla, var))
            }
            Term::App { function, terms } => {
                let mut conjuncts = vec![];
                let mut new_terms = terms
                    .iter()
                    .map(|t| {
                        if let Some((fmla, var)) = self.flatten_term(t) {
                            conjuncts.push(fmla);
                            var.into()
                        } else {
                            t.clone()
                        }
                    })
                    .collect::<Vec<Term>>();

                let var = V(self.flattening_generator.next());
                new_terms.push(var.clone().into());

                let pred = Pred(
                    self.function_predicate_generator
                        .symbol(function.0.to_string()),
                );
                let fmla = pred.app(new_terms);
                // Preserving the topological order among variables:
                if !conjuncts.is_empty() {
                    let mut iter = conjuncts.into_iter();
                    let first = iter.next().unwrap();
                    let conjuncts = iter.fold(first, |f1, f2| f1.and(f2));
                    Some((conjuncts.and(fmla), var))
                } else {
                    Some((fmla, var))
                }
            }
        }
    }

    // Replaces variables appearing in more than one position with fresh variables.
    // It asumes that the input is already flattened and does not contain complex terms.
    fn expand_equality(
        &self,
        formula: &Formula,
        vars: &mut HashMap<V, i32>,
    ) -> Result<Formula, Error> {
        match formula {
            Formula::Top | Formula::Bottom => Ok(formula.clone()),
            Formula::Atom { predicate, terms } => {
                let mut equations = Vec::new();
                let mut new_terms = Vec::<Term>::new();
                for term in terms {
                    match term {
                        Term::Var { variable } => {
                            vars.entry(variable.clone())
                                .and_modify(|count| {
                                    let new_var = V(self
                                        .equality_generator
                                        .indexed_symbol(variable.to_string(), *count));
                                    let eq_pred = Pred(self.equality_symbol.clone());
                                    equations.push(eq_pred.app(vec![
                                        variable.clone().into(),
                                        new_var.clone().into(),
                                    ]));
                                    new_terms.push(new_var.into());
                                    *count += 1;
                                })
                                .or_insert_with(|| {
                                    new_terms.push(Term::Var {
                                        variable: variable.clone(),
                                    });
                                    0
                                });
                        }
                        _ => return Err(Error::EqualityExpandNonVar { term: term.clone() }),
                    }
                }
                Ok(equations
                    .into_iter()
                    .fold(predicate.clone().app(new_terms), |fmla, eq| fmla.and(eq)))
            }
            Formula::And { left, right } => {
                let left = self.expand_equality(left, vars)?;
                let right = self.expand_equality(right, vars)?;
                Ok(left.and(right))
            }
            Formula::Or { left, right } => {
                let left = self.expand_equality(left, vars)?;
                let right = self.expand_equality(right, vars)?;
                Ok(left.or(right))
            }
            _ => Err(Error::EqualityExpandUnsupported {
                formula: formula.clone(),
            }),
        }
    }
}

/// Given a `formula`, and a list of variables `range`, ensures that every
/// variable in `range` appears at least once in `formula`. This is done by conjoining atomic
/// formulae in the form of `RR(v)` where `RR` is a "range restriction" predicate with
/// `symbol` as the predicate symbol. The transformation fails if the `formula` is not
/// relationalized.
/// The underlying algorithm assumes that the input is negation and quantifier-free;
/// that is, `¬`, `→`, `⇔`, `∃`, `∀` are not allowed as connectives.
///
/// **Note**: the term "range restriction" is borrowed from the database literature.
///
/// **Example**:
/// ```rust
/// use razor_fol::syntax::{Formula};
/// use razor_fol::v;
/// use razor_fol::transform::relationalize::range_restrict;
///
/// let fmla = "P(x) & Q(y)".parse::<Formula>().unwrap();
/// let result = range_restrict(&fmla, &vec![v!(x), v!(z)], "RR").unwrap();
/// assert_eq!(
///     r"(P(x) ∧ Q(y)) ∧ RR(z)",
///     result.to_string()
/// );
///
/// let fmla = "~P(x)".parse::<Formula>().unwrap();
/// assert!(range_restrict(&fmla, &vec![v!(x), v!(z)], "RR").is_err());
/// ```
pub fn range_restrict(formula: &Formula, range: &[V], symbol: &str) -> Result<Formula, Error> {
    let formula = match formula {
        Formula::Bottom => formula.clone(),
        Formula::Top => {
            if let Some(conjunct) = range_restrict_conjunct(range, symbol) {
                conjunct
            } else {
                formula.clone()
            }
        }
        Formula::Atom { .. } | Formula::And { .. } => {
            let free = formula.free_vars();
            let mut range = Vec::from(range);
            range.retain(|x| !free.contains(&x));
            if let Some(conjunct) = range_restrict_conjunct(&range, symbol) {
                formula.clone().and(conjunct)
            } else {
                formula.clone()
            }
        }
        Formula::Or { left, right } => {
            let left = range_restrict(left, range, symbol)?;
            let right = range_restrict(right, range, symbol)?;
            left.or(right)
        }
        _ => {
            return Err(Error::RangeRestrictUnsupported {
                formula: formula.clone(),
            })
        }
    };
    Ok(formula)
}

// A helper for `range_restrict` to build range_restriction conjuncts.
fn range_restrict_conjunct(range: &[V], symbol: &str) -> Option<Formula> {
    if range.is_empty() {
        return None;
    }

    let mut formula = Pred(symbol.into()).app(vec![range[0].clone().into()]);
    let mut vs = &range[1..];

    while !vs.is_empty() {
        let eq = Pred(symbol.into()).app(vec![vs[0].clone().into()]);
        formula = formula.and(eq);
        vs = &vs[1..];
    }

    Some(formula)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{formula, v};

    #[test]
    fn test_relationalize_formula() -> Result<(), Error> {
        assert_eq! {
            "⊤",
            Relationalizer::new().flatten_formula(&formula!('|'))?.to_string(),
        };
        assert_eq! {
            "⟘",
            Relationalizer::new().flatten_formula(&formula!(_|_))?.to_string(),
        };
        assert_eq! {
            "P()",
            Relationalizer::new().flatten_formula(&formula!(P()))?.to_string(),
        };
        assert_eq! {
            "P(x, y)",
            Relationalizer::new().flatten_formula(&formula!(P(x, y)))?.to_string(),
        };
        assert_eq! {
            "=(x, y)",
            Relationalizer::new().flatten_formula(&formula!((x) = (y)))?.to_string(),
        }
        assert_eq! {
            r"@c(?0) ∧ =(x, ?0)",
            Relationalizer::new().flatten_formula(&formula!((x) = (@c)))?.to_string(),
        }
        assert_eq! {
            r"(@c(?0) ∧ @d(?1)) ∧ =(?0, ?1)",
            Relationalizer::new().flatten_formula(&formula!((@c) = (@d)))?.to_string(),
        }
        assert_eq! {
            r"@c(?0) ∧ P(?0)",
            Relationalizer::new().flatten_formula(&formula!(P(@c)))?.to_string(),
        };
        assert_eq! {
            r"@c(?0) ∧ P(x, ?0)",
            Relationalizer::new().flatten_formula(&formula!(P(x, @c)))?.to_string(),
        };
        assert_eq! {
            r"(@c(?0) ∧ @d(?1)) ∧ P(?0, ?1)",
            Relationalizer::new().flatten_formula(&formula!(P(@c, @d)))?.to_string(),
        };
        assert_eq! {
            r"$f(x, ?0) ∧ P(?0)",
            Relationalizer::new().flatten_formula(&formula!(P(f(x))))?.to_string(),
        };
        assert_eq! {
            "($g(x, ?0) ∧ $f(?0, ?1)) ∧ P(?1)",
            Relationalizer::new().flatten_formula(&formula!(P(f(g(x)))))?.to_string(),
        };
        assert_eq! {
            "(($g(x, ?0) ∧ $f(?0, ?1)) ∧ $f(y, ?2)) ∧ P(?1, ?2)",
            Relationalizer::new().flatten_formula(&formula!(P(f(g(x)), f(y))))?.to_string(),
        };
        assert_eq! {
            "P(x) ∧ Q(y)",
            Relationalizer::new().flatten_formula(&formula!((P(x)) & (Q(y))))?.to_string(),
        };
        assert_eq! {
            "(@c(?0) ∧ P(?0)) ∧ (@d(?1) ∧ Q(?1))",
            Relationalizer::new().flatten_formula(&formula!((P(@c)) & (Q(@d))))?.to_string(),
        };
        assert_eq! {
            "P(x) ∨ Q(y)",
            Relationalizer::new().flatten_formula(&formula!((P(x)) | (Q(y))))?.to_string(),
        };
        assert_eq! {
            "(@c(?0) ∧ P(?0)) ∨ (@d(?1) ∧ Q(?1))",
            Relationalizer::new().flatten_formula(&formula!((P(@c)) | (Q(@d))))?.to_string(),
        };

        assert!(Relationalizer::new()
            .flatten_formula(&formula!(~[P()]))
            .is_err());
        assert!(Relationalizer::new()
            .flatten_formula(&formula!([P()] -> [Q()]))
            .is_err());
        assert!(Relationalizer::new()
            .flatten_formula(&formula!([P()] <=> [Q()]))
            .is_err());
        assert!(Relationalizer::new()
            .flatten_formula(&formula!(?x.[P(x)]))
            .is_err());
        assert!(Relationalizer::new()
            .flatten_formula(&formula!(!x.[P(x)]))
            .is_err());

        Ok(())
    }

    #[test]
    fn test_expand_equality() -> Result<(), Error> {
        assert_eq!(
            "⊤",
            Relationalizer::new()
                .expand_equality(&formula!('|'), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "⟘",
            Relationalizer::new()
                .expand_equality(&formula!(_|_), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "P()",
            Relationalizer::new()
                .expand_equality(&formula!(P()), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "P(x, y)",
            Relationalizer::new()
                .expand_equality(&formula!(P(x, y)), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "P(x, ~x:0) ∧ =(x, ~x:0)",
            Relationalizer::new()
                .expand_equality(&formula!(P(x, x)), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "P(x, y) ∧ (Q(~x:0) ∧ =(x, ~x:0))",
            Relationalizer::new()
                .expand_equality(&formula!([P(x, y)] & [Q(x)]), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "P(x, y) ∧ ((Q(~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            Relationalizer::new()
                .expand_equality(&formula!([P(x, y)] & [Q(x, y)]), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "P(x) ∧ ((Q(y, ~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            Relationalizer::new()
                .expand_equality(&formula!([P(x)] & [Q(y, x, y)]), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "(P(x) ∧ (Q(~x:0) ∧ =(x, ~x:0))) ∧ (R(~x:1) ∧ =(x, ~x:1))",
            Relationalizer::new()
                .expand_equality(
                    &formula!({ [P(x)] & [Q(x)] } & { R(x) }),
                    &mut HashMap::new()
                )?
                .to_string(),
        );
        assert_eq!(
            "P(x, y) ∨ (Q(~x:0) ∧ =(x, ~x:0))",
            Relationalizer::new()
                .expand_equality(&formula!([P(x, y)] | [Q(x)]), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "P(x, y) ∨ ((Q(~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            Relationalizer::new()
                .expand_equality(&formula!([P(x, y)] | [Q(x, y)]), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "P(x) ∨ ((Q(y, ~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            Relationalizer::new()
                .expand_equality(&formula!([P(x)] | [Q(y, x, y)]), &mut HashMap::new())?
                .to_string(),
        );
        assert_eq!(
            "(P(x) ∨ (Q(~x:0) ∧ =(x, ~x:0))) ∨ (R(~x:1) ∧ =(x, ~x:1))",
            Relationalizer::new()
                .expand_equality(
                    &formula!({ [P(x)] | [Q(x)] } | { R(x) }),
                    &mut HashMap::new()
                )?
                .to_string(),
        );

        assert!(Relationalizer::new()
            .expand_equality(&formula!(P(@c)), &mut HashMap::new())
            .is_err());
        assert!(Relationalizer::new()
            .expand_equality(&formula!(P(f(x))), &mut HashMap::new())
            .is_err());
        assert!(Relationalizer::new()
            .expand_equality(&formula!(~[P()]), &mut HashMap::new())
            .is_err());
        assert!(Relationalizer::new()
            .expand_equality(&formula!([P()] -> [Q()]), &mut HashMap::new())
            .is_err());
        assert!(Relationalizer::new()
            .expand_equality(&formula!([P()] <=> [Q()]), &mut HashMap::new())
            .is_err());
        assert!(Relationalizer::new()
            .expand_equality(&formula!(?x.[P(x)]), &mut HashMap::new())
            .is_err());
        assert!(Relationalizer::new()
            .expand_equality(&formula!(!x.[P(x)]), &mut HashMap::new())
            .is_err());

        Ok(())
    }

    #[test]
    fn test_range_restrict() -> Result<(), Error> {
        let rr = "RR";
        assert_eq!(
            "⊤",
            range_restrict(&formula!('|'), &vec![], rr)?.to_string()
        );
        assert_eq!(
            "RR(x)",
            range_restrict(&formula!('|'), &vec![v!(x)], rr)?.to_string()
        );
        assert_eq!(
            "RR(x) ∧ RR(y)",
            range_restrict(&formula!('|'), &vec![v!(x), v!(y)], rr)?.to_string()
        );
        assert_eq!(
            "⟘",
            range_restrict(&formula!(_|_), &vec![], rr)?.to_string()
        );

        assert_eq!(
            "P(x)",
            range_restrict(&formula!(P(x)), &vec![], rr)?.to_string()
        );
        assert_eq!(
            "P(w, x, y) ∧ RR(z)",
            range_restrict(&formula!(P(w, x, y)), &vec![v!(x), v!(y), v!(z)], rr)?.to_string()
        );

        assert_eq!(
            "P(x) ∧ Q(y)",
            range_restrict(&formula!([P(x)] & [Q(y)]), &vec![], rr)?.to_string()
        );
        assert_eq!(
            "(P(v, w) ∧ Q(x)) ∧ (RR(y) ∧ RR(z))",
            range_restrict(
                &formula!([P(v, w)] & [Q(x)]),
                &vec![v!(v), v!(w), v!(x), v!(y), v!(z)],
                rr
            )?
            .to_string()
        );

        assert_eq!(
            "P(x) ∨ Q(y)",
            range_restrict(&formula!([P(x)] | [Q(y)]), &vec![], rr)?.to_string()
        );

        assert_eq!(
            "(P(x) ∧ RR(y)) ∨ (Q(y) ∧ RR(x))",
            range_restrict(&formula!([P(x)] | [Q(y)]), &vec![v!(x), v!(y)], rr)?.to_string()
        );

        Ok(())
    }

    #[test]
    fn test_relationalize() -> Result<(), Error> {
        assert_eq!(
            "$f(y, ?0) ∧ (P(x, ~?0:0) ∧ =(?0, ~?0:0))",
            Relationalizer::new()
                .relationalize(&formula!(P(x, f(y))))?
                .to_string()
        );
        assert_eq!(
            "$f(x, ?0) ∧ ((P(~x:0, ~?0:0) ∧ =(x, ~x:0)) ∧ =(?0, ~?0:0))",
            Relationalizer::new()
                .relationalize(&formula!(P(x, f(x))))?
                .to_string()
        );

        Ok(())
    }
}
