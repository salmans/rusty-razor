/*! Implements a relationalization algorithm for formulae.*/

use super::Error;
use crate::syntax::{symbol::Generator, Formula, Pred, Term, V};
use std::collections::HashMap;

/// Is a wrapper around [`Formula`] that represents a relationalized formula.
///
/// **Hint**: A relationalized formula contains only (flat) variable terms with
/// no function symbol nor constants. [`Relationalizer`] transforms suitable formulae
/// to a relational form.
///
/// [`Formula`]: ../syntax/enum.Formula.html
/// [`Relationalizer`]: ./struct.Relationalizer.html
#[derive(Clone, Debug)]
pub struct Relational(Formula);

impl Relational {
    /// Returns a reference to the formula wrapped in the receiver.
    #[inline(always)]
    pub fn formula(&self) -> &Formula {
        &self.0
    }
}

impl From<Relational> for Formula {
    fn from(relational: Relational) -> Self {
        relational.0
    }
}

/// Provides the relationalization algorithm through its [`relationalize`] method.
///
/// [`relationalize`]: ./struct.Relationalizer.html#method.relationalize
pub struct Relationalizer {
    // Is the symbol used to convert equality to a predicate.
    equality_symbol: String,

    // Is the [`Generator`] instance used to generate variable names used as placeholders
    // in flattened formulae.
    flattening_generator: Generator,

    // Is the [`Generator`] instance used to create predicate symbols for functions.
    function_predicate_generator: Generator,

    // Is the [`Generator`] instance used to create predicate symbols for constants.
    constant_predicate_generator: Generator,
}

impl Relationalizer {
    /// Creates a new `Relationalizer` instance with default generators and symbols:
    ///   * The equality symbol is `=`.
    ///   * Variables introduced by flattening are prefixed with `?`.
    ///   * Function predicates are prefixed with `$`.
    pub fn new() -> Self {
        Self {
            equality_symbol: "=".into(),
            flattening_generator: Generator::new().set_prefix("?"),
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

    /// Use `generator` to create function predicate names.
    pub fn set_predicate_generator(&mut self, generator: Generator) {
        self.function_predicate_generator = generator;
    }

    /// Consumes the `Relationalizer`, applies the relationalization algorithm on `formula` and
    /// returns the relationalized formula if it succeeds.
    /// The underlying algorithm assumes that the input is negation and quantifier-free;
    /// that is, `¬`, `→`, `⇔`, `∃`, `∀` are not allowed as connectives. Relationalization consists of
    /// applying the following rewrites on the input formula:
    ///   * A constant `'c` is replaced by a predicate `C(x)`.
    ///   * A complex term `f(x_1, ..., x_n)` is replaced by a fresh variable `v` and an atomic
    /// formula `F(x_1, ..., x_n, v)` is conjoined with the input formula.
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
    /// let transformed = Relationalizer::new().transform(&fmla).unwrap();
    /// assert_eq!(
    ///     r"($f(x, ?0) ∧ P(?0)) ∧ (@c(?1) ∧ Q(?1))",
    ///     transformed.formula().to_string()
    /// );
    ///
    /// let fmla = "~P(x)".parse::<Formula>().unwrap();
    /// assert!(Relationalizer::new().transform(&fmla).is_err());    
    /// ```
    pub fn transform(&mut self, formula: &Formula) -> Result<Relational, Error> {
        self.constant_predicate_generator.reset();
        self.function_predicate_generator.reset();
        self.flattening_generator.reset();

        self.flatten_formula(formula).map(Relational)
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
}

/// Is used to expand implicit equations by replacing variables that appear in more than
/// one position of a formula with freshly generated variables. The expansion algorithm
/// is provided by the [`expand_equality`] method.
///
/// [`expand_eqaulity`]: ./struct.EqualityExpander.html#method.expand_equality
pub struct EqualityExpander {
    // Is the symbol used to convert equality to a predicate.
    equality_symbol: String,

    // Is the [`Generator`] instance used to generate new variable names when variables
    // appear in more than one position.
    equality_generator: Generator,
}

impl EqualityExpander {
    /// Creates a new `EqualityExpander` instance with default generators and symbols:
    /// * The equality symbol is `=`.
    /// * Variables appearing in more than one position are distinguished with `~` as the
    /// prefix, followed by `:` and a unique index.
    pub fn new() -> Self {
        Self {
            equality_symbol: "=".into(),
            equality_generator: Generator::new().set_prefix("~").set_delimiter(":"),
        }
    }

    /// Use `symbol` for equality predicates.
    pub fn set_equality_symbol<S: Into<String>>(&mut self, symbol: S) {
        self.equality_symbol = symbol.into();
    }

    /// Use `generator` to distinguish variables that appear in more than one positions.
    pub fn set_equality_generator(&mut self, generator: Generator) {
        self.equality_generator = generator;
    }

    fn helper(&self, formula: &Formula, vars: &mut HashMap<V, i32>) -> Result<Formula, Error> {
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
                let left = self.helper(left, vars)?;
                let right = self.helper(right, vars)?;
                Ok(left.and(right))
            }
            Formula::Or { left, right } => {
                let left = self.helper(left, vars)?;
                let right = self.helper(right, vars)?;
                Ok(left.or(right))
            }
            _ => Err(Error::EqualityExpandUnsupported {
                formula: formula.clone(),
            }),
        }
    }

    /// Consumes the `EqualityExpander` and replaces any varialbe `v` that appears in more than
    /// one position of `formula` with a fresh variable `y` and an atom `=(v, y)` is conjoined
    /// with `formula`.
    ///
    /// **Note**:
    /// The method asumes that the input is already flattened and does not contain complex terms.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::relationalize::{Relationalizer, EqualityExpander};
    ///
    /// let fmla = "P(f(x)) & Q('c)".parse::<Formula>().unwrap();
    /// let relational = Relationalizer::new().transform(&fmla).unwrap();
    /// let transformed = EqualityExpander::new().transform(&relational).unwrap();
    /// assert_eq!(
    ///     r"($f(x, ?0) ∧ (P(~?0:0) ∧ =(?0, ~?0:0))) ∧ (@c(?1) ∧ (Q(~?1:0) ∧ =(?1, ~?1:0)))",
    ///     transformed.to_string()
    /// );
    ///
    /// let fmla = "~P(x)".parse::<Formula>().unwrap();
    /// assert!(Relationalizer::new().transform(&fmla).is_err());
    /// ```
    pub fn transform(&self, formula: &Relational) -> Result<Relational, Error> {
        self.helper(formula.formula(), &mut HashMap::new())
            .map(Relational)
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
/// use razor_fol::transform::relationalize::{Relationalizer, range_restrict};
///
/// let fmla = "P(x) & Q(y)".parse::<Formula>().unwrap();
/// let relational = Relationalizer::new().transform(&fmla).unwrap();
/// let transformed = range_restrict(&relational, &vec![v!(x), v!(z)], "RR").unwrap();
/// assert_eq!(
///     r"(P(x) ∧ Q(y)) ∧ RR(z)",
///     transformed.formula().to_string()
/// );
/// ```
pub fn range_restrict(
    formula: &Relational,
    range: &[V],
    symbol: &str,
) -> Result<Relational, Error> {
    rr_helper(formula.formula(), range, symbol).map(Relational)
}

// Is a helper for range_restrict that works on the wrapped formula inside the input `Relational`
#[inline(always)]
fn rr_helper(formula: &Formula, range: &[V], symbol: &str) -> Result<Formula, Error> {
    let formula = match formula {
        Formula::Bottom => formula.clone(),
        Formula::Top => {
            if let Some(conjunct) = rr_conjunct(range, symbol) {
                conjunct
            } else {
                formula.clone()
            }
        }
        Formula::Atom { .. } | Formula::And { .. } => {
            let free = formula.free_vars();
            let mut range = Vec::from(range);
            range.retain(|x| !free.contains(&x));
            if let Some(conjunct) = rr_conjunct(&range, symbol) {
                formula.clone().and(conjunct)
            } else {
                formula.clone()
            }
        }
        Formula::Or { left, right } => {
            let left = rr_helper(left, range, symbol)?;
            let right = rr_helper(right, range, symbol)?;
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

// Is a helper for `range_restrict` to build range_restriction conjuncts.
#[inline(always)]
fn rr_conjunct(range: &[V], symbol: &str) -> Option<Formula> {
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
        fn expand_equality(formula: &Formula) -> Result<Formula, Error> {
            EqualityExpander::new().helper(formula, &mut HashMap::new())
        }

        assert_eq!("⊤", expand_equality(&formula!('|'))?.to_string(),);
        assert_eq!("⟘", expand_equality(&formula!(_|_))?.to_string(),);
        assert_eq!("P()", expand_equality(&formula!(P()))?.to_string(),);
        assert_eq!("P(x, y)", expand_equality(&formula!(P(x, y)))?.to_string(),);
        assert_eq!(
            "P(x, ~x:0) ∧ =(x, ~x:0)",
            expand_equality(&formula!(P(x, x)))?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∧ (Q(~x:0) ∧ =(x, ~x:0))",
            expand_equality(&formula!([P(x, y)] & [Q(x)]))?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∧ ((Q(~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            expand_equality(&formula!([P(x, y)] & [Q(x, y)]))?.to_string(),
        );
        assert_eq!(
            "P(x) ∧ ((Q(y, ~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            expand_equality(&formula!([P(x)] & [Q(y, x, y)]))?.to_string(),
        );
        assert_eq!(
            "(P(x) ∧ (Q(~x:0) ∧ =(x, ~x:0))) ∧ (R(~x:1) ∧ =(x, ~x:1))",
            expand_equality(&formula!({ [P(x)] & [Q(x)] } & { R(x) }))?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∨ (Q(~x:0) ∧ =(x, ~x:0))",
            expand_equality(&formula!([P(x, y)] | [Q(x)]))?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∨ ((Q(~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            expand_equality(&formula!([P(x, y)] | [Q(x, y)]))?.to_string(),
        );
        assert_eq!(
            "P(x) ∨ ((Q(y, ~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            expand_equality(&formula!([P(x)] | [Q(y, x, y)]))?.to_string(),
        );
        assert_eq!(
            "(P(x) ∨ (Q(~x:0) ∧ =(x, ~x:0))) ∨ (R(~x:1) ∧ =(x, ~x:1))",
            expand_equality(&formula!({ [P(x)] | [Q(x)] } | { R(x) }))?.to_string(),
        );

        assert!(expand_equality(&formula!(P(@c))).is_err());
        assert!(expand_equality(&formula!(P(f(x)))).is_err());
        assert!(expand_equality(&formula!(~[P()])).is_err());
        assert!(expand_equality(&formula!([P()] -> [Q()])).is_err());
        assert!(expand_equality(&formula!([P()] <=> [Q()])).is_err());
        assert!(expand_equality(&formula!(?x.[P(x)])).is_err());
        assert!(expand_equality(&formula!(!x.[P(x)])).is_err());

        Ok(())
    }

    #[test]
    fn test_range_restrict() -> Result<(), Error> {
        let rr = "RR";
        assert_eq!("⊤", rr_helper(&formula!('|'), &vec![], rr)?.to_string());
        assert_eq!(
            "RR(x)",
            rr_helper(&formula!('|'), &vec![v!(x)], rr)?.to_string()
        );
        assert_eq!(
            "RR(x) ∧ RR(y)",
            rr_helper(&formula!('|'), &vec![v!(x), v!(y)], rr)?.to_string()
        );
        assert_eq!("⟘", rr_helper(&formula!(_|_), &vec![], rr)?.to_string());

        assert_eq!("P(x)", rr_helper(&formula!(P(x)), &vec![], rr)?.to_string());
        assert_eq!(
            "P(w, x, y) ∧ RR(z)",
            rr_helper(&formula!(P(w, x, y)), &vec![v!(x), v!(y), v!(z)], rr)?.to_string()
        );

        assert_eq!(
            "P(x) ∧ Q(y)",
            rr_helper(&formula!([P(x)] & [Q(y)]), &vec![], rr)?.to_string()
        );
        assert_eq!(
            "(P(v, w) ∧ Q(x)) ∧ (RR(y) ∧ RR(z))",
            rr_helper(
                &formula!([P(v, w)] & [Q(x)]),
                &vec![v!(v), v!(w), v!(x), v!(y), v!(z)],
                rr
            )?
            .to_string()
        );

        assert_eq!(
            "P(x) ∨ Q(y)",
            rr_helper(&formula!([P(x)] | [Q(y)]), &vec![], rr)?.to_string()
        );

        assert_eq!(
            "(P(x) ∧ RR(y)) ∨ (Q(y) ∧ RR(x))",
            rr_helper(&formula!([P(x)] | [Q(y)]), &vec![v!(x), v!(y)], rr)?.to_string()
        );

        Ok(())
    }

    #[test]
    fn test_relationalize() -> Result<(), Error> {
        assert_eq!(
            "$f(y, ?0) ∧ P(x, ?0)",
            Relationalizer::new()
                .transform(&formula!(P(x, f(y))))?
                .formula()
                .to_string()
        );
        assert_eq!(
            "$f(x, ?0) ∧ P(x, ?0)",
            Relationalizer::new()
                .transform(&formula!(P(x, f(x))))?
                .formula()
                .to_string()
        );

        Ok(())
    }
}
