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

    // Maintains a list of generated existential variables during the transformation of
    // the last formula.
    generated_variables: Vec<V>,
}

macro_rules! term_as_var {
    ($term:expr) => {{
        match $term {
            Term::Var { variable: v } => v,
            _ => unreachable!(),
        }
    }};
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
            generated_variables: Vec::new(),
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
        let transformed = self.flatten_formula(formula);

        let result = transformed.map(|t| {
            let simplified = self.simplify_equations(&t);
            let result = remove_reflexive_equations(&simplified, &self.equality_symbol);
            Relational(result.unwrap_or(Formula::Top))
        });
        self.reset();

        result
    }

    // Resets the Relationalizer, preparing for the next transformation.
    fn reset(&mut self) {
        self.constant_predicate_generator.reset();
        self.function_predicate_generator.reset();
        self.flattening_generator.reset();
        self.generated_variables.clear();
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

    // Generates a new variable using the `flattening_generator` and keeps track of it in
    // `generated_variables`.
    fn generate_variable(&mut self) -> V {
        let var = V(self.flattening_generator.next().into());
        self.generated_variables.push(var.clone());
        var
    }

    // Recursively flattens a term and returns the resulting formula together with a placeholder variable
    // for the term. Nothing needs to be done if the input term is a variable.
    fn flatten_term(&mut self, term: &Term) -> Option<(Formula, V)> {
        match term {
            Term::Var { .. } => None,
            Term::Const { constant } => {
                let var = self.generate_variable();
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

                let var = self.generate_variable();
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

    // Simplify tries to minimize the use of existential variables (generated by relationalize) by replacing
    // them with universal or other existential variables that are equal with them.
    fn simplify_equations(&self, formula: &Formula) -> Formula {
        let mut map = HashMap::new();
        self.equation_rewrites(formula, &mut map);

        use super::substitution::TermBased;
        let sub = |v: &V| {
            let variable = if map.contains_key(v) {
                (*map.get(v).unwrap()).clone()
            } else {
                v.clone()
            };
            Term::Var { variable }
        };
        formula.substitute(&sub)
    }

    // As a helper for `simplify_equations` collects a set of rewrite rules as entries of a map, corresponding
    // to equations with an existential variable on one side.
    fn equation_rewrites<'a>(&self, formula: &'a Formula, map: &mut HashMap<&'a V, &'a V>) {
        match formula {
            Formula::Atom { predicate, terms } => {
                if predicate.0 == self.equality_symbol {
                    assert_eq!(2, terms.len());
                    let left = terms.get(0).unwrap();
                    let right = terms.get(1).unwrap();

                    let l = term_as_var!(left);
                    let r = term_as_var!(right);

                    let l_generated = self.generated_variables.contains(&l);
                    let r_generated = self.generated_variables.contains(&r);

                    match (l_generated, r_generated) {
                        (false, true) => {
                            map.insert(r, l);
                        }
                        (true, false) => {
                            map.insert(l, r);
                        }
                        (true, true) => {
                            if map.contains_key(l) {
                                map.insert(r, map.get(l).unwrap());
                            } else if map.contains_key(r) {
                                map.insert(l, map.get(r).unwrap());
                            } else {
                                map.insert(l, r);
                            }
                        }
                        _ => {}
                    }
                }
            }
            Formula::Not { formula } => {
                self.equation_rewrites(formula, map);
            }
            Formula::And { left, right } => {
                self.equation_rewrites(left, map);
                self.equation_rewrites(right, map);
            }
            Formula::Or { left, right } => {
                self.equation_rewrites(left, map);
                self.equation_rewrites(right, map);
            }
            Formula::Implies { left, right } => {
                self.equation_rewrites(left, map);
                self.equation_rewrites(right, map);
            }
            Formula::Iff { left, right } => {
                self.equation_rewrites(left, map);
                self.equation_rewrites(right, map);
            }
            Formula::Exists { formula, .. } => {
                self.equation_rewrites(formula, map);
            }
            Formula::Forall { formula, .. } => {
                self.equation_rewrites(formula, map);
            }
            _ => {}
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

    /// Replaces replaces any varialbe `v` that appears in more than one position of `formula`
    /// with a fresh variable `y` and an atom `=(v, y)` is conjoined with `formula`.
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
    ///     transformed.formula().to_string()
    /// );
    ///
    /// let fmla = "~P(x)".parse::<Formula>().unwrap();
    /// assert!(Relationalizer::new().transform(&fmla).is_err());
    /// ```
    pub fn transform(&self, formula: &Relational) -> Result<Relational, Error> {
        let transformed = self.helper(formula.formula(), &mut HashMap::new());
        transformed.map(|t| {
            let result = remove_reflexive_equations(&t, &self.equality_symbol);
            Relational(result.unwrap_or(Formula::Top))
        })
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

fn combine_binary<F>(first: Option<Formula>, second: Option<Formula>, f: F) -> Option<Formula>
where
    F: FnOnce(Formula, Formula) -> Formula,
{
    match (&first, &second) {
        (None, None) => None,
        (None, Some(_)) => second,
        (Some(_), None) => first,
        (Some(_), Some(_)) => Some(f(first.unwrap(), second.unwrap())),
    }
}

fn remove_reflexive_equations(formula: &Formula, eq_symbol: &str) -> Option<Formula> {
    use crate::syntax::{exists, forall, not};
    match &formula {
        Formula::Atom { predicate, terms } => {
            if predicate.0 == eq_symbol {
                assert_eq!(2, terms.len());
                let left = terms.get(0).unwrap();
                let right = terms.get(1).unwrap();
                if left == right {
                    None
                } else {
                    Some(formula.clone())
                }
            } else {
                Some(formula.clone())
            }
        }
        Formula::Equals { left, right } => {
            if left == right {
                None
            } else {
                Some(formula.clone())
            }
        }
        Formula::Not { formula } => remove_reflexive_equations(formula, eq_symbol).map(|f| not(f)),
        Formula::And { left, right } => combine_binary(
            remove_reflexive_equations(left, eq_symbol),
            remove_reflexive_equations(right, eq_symbol),
            Formula::and,
        ),
        Formula::Or { left, right } => combine_binary(
            remove_reflexive_equations(left, eq_symbol),
            remove_reflexive_equations(right, eq_symbol),
            Formula::or,
        ),
        Formula::Implies { left, right } => combine_binary(
            remove_reflexive_equations(left, eq_symbol),
            remove_reflexive_equations(right, eq_symbol),
            Formula::implies,
        ),
        Formula::Iff { left, right } => combine_binary(
            remove_reflexive_equations(left, eq_symbol),
            remove_reflexive_equations(right, eq_symbol),
            Formula::iff,
        ),
        Formula::Exists { variables, formula } => {
            remove_reflexive_equations(formula, eq_symbol).map(|f| exists(variables.clone(), f))
        }
        Formula::Forall { variables, formula } => {
            remove_reflexive_equations(formula, eq_symbol).map(|f| forall(variables.clone(), f))
        }
        _ => Some(formula.clone()),
    }
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
            "$f(x, y)",
            Relationalizer::new()
                .transform(&formula!([f(x)] = [y]))?
                .formula()
                .to_string()
        );
        assert_eq!(
            "$f(x, ?1) ∧ $g(y, ?1)",
            Relationalizer::new()
                .transform(&formula!([f(x)] = [g(y)]))?
                .formula()
                .to_string()
        );
        assert_eq!(
            "($f(x, ?1) ∧ $g(y, ?1)) ∨ $f(x, y)",
            Relationalizer::new()
                .transform(&formula!({ [f(x)] = [g(y)] } | { [f(x)] = [y] }))?
                .formula()
                .to_string()
        );
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
