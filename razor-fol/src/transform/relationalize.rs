/*! Implements a relationalization algorithm for formulae.*/
use super::Error;
use crate::syntax::{symbol::Generator, Formula, Pred, Term, FOF, V};
use std::collections::HashMap;

/// Is a wrapper around [`FOF`] that represents a relationalized first-order formula.
///
/// **Hint**: A relationalized formula contains only (flat) variable terms with
/// no function symbol nor constants. [`Relationalizer`] transforms suitable formulae
/// to a relational form.
///
/// [`FOF`]: crate::syntax::FOF
#[derive(Clone, Debug)]
pub struct Relational(FOF);

impl Relational {
    /// Returns a reference to the first-order formula wrapped in the receiver.
    #[inline(always)]
    pub fn formula(&self) -> &FOF {
        &self.0
    }
}

impl From<Relational> for FOF {
    fn from(relational: Relational) -> Self {
        relational.0
    }
}

/// Provides the relationalization algorithm through the [`transform`] method.
///
/// [`transform`]: Relationalizer::transform()
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

    /// Applies the relationalization algorithm on `formula` and returns the relationalized
    /// formula if it succeeds.
    /// The underlying algorithm assumes that the input is negation and quantifier-free;
    /// that is, `¬`, `→`, `⇔`, `∃`, `∀` are not allowed as connectives. Relationalization consists of
    /// applying the following rewrites on the input formula:
    ///   * A constant `'c` rewrites to a predicate `C(x)`.
    ///   * A complex term `f(x_1, ..., x_n)` rewrites to a fresh variable `v` and an atomic
    /// formula `F(x_1, ..., x_n, v)` is conjoined with the input formula.
    ///   * An equation `v = y` rewrites to an atomic formula `=(x, y)`.
    ///
    /// **Note**:
    /// The resulting formula is semantically isomorphic to the input *only* in presence of equality and
    /// function integrity axioms in the theory.
    ///
    /// **Note**:
    /// In the resulting formula, the new (placeholder) variables are sorted topologically from left to write
    /// where the ordering relation is the dependency between the new variables.
    /// A varialbe `v` depends on a variable `y` if for a new function predicate, namely `F`,
    /// `F(..., y,..., v)` is a conjunct in the formula (that is, the result of the
    /// function replaced by `F`, applied to its arguments, depends on `y`).
    ///
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::relationalize::Relationalizer;
    ///
    /// let fmla = "P(f(x)) & Q('c)".parse::<FOF>().unwrap();
    /// let transformed = Relationalizer::default().transform(&fmla).unwrap();
    /// assert_eq!(
    ///     r"($f(x, ?0) ∧ P(?0)) ∧ (@c(?1) ∧ Q(?1))",
    ///     transformed.formula().to_string()
    /// );
    ///
    /// let fmla = "~P(x)".parse::<FOF>().unwrap();
    /// assert!(Relationalizer::default().transform(&fmla).is_err()); // cannot relationalize
    /// ```
    pub fn transform(&mut self, formula: &FOF) -> Result<Relational, Error> {
        let flattened = self.flatten_formula(formula);
        let result = flattened.map(|t| {
            let simplified = self.simplify_equations(&t);
            let result = remove_reflexive_equations(&simplified, &self.equality_symbol);
            Relational(result.unwrap_or(FOF::Top))
        });
        self.reset(); // prepare for next call to `transform`

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
    fn flatten_formula(&mut self, formula: &FOF) -> Result<FOF, Error> {
        match formula {
            FOF::Top | FOF::Bottom => Ok(formula.clone()),
            FOF::Atom(this) => {
                let mut conjuncts = vec![];
                let new_terms = this
                    .terms()
                    .iter()
                    .map(|t| {
                        self.flatten_term(t)
                            .map(|(fmla, var)| {
                                conjuncts.push(fmla);
                                var.into()
                            })
                            .unwrap_or_else(|| t.clone())
                    })
                    .collect::<Vec<_>>();

                let fmla = this.predicate().clone().app(new_terms);
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
            FOF::Equals(this) => self.flatten_formula(
                &Pred(self.equality_symbol.clone())
                    .app(vec![this.left().clone(), this.right().clone()]),
            ),
            FOF::And(this) => {
                let left = self.flatten_formula(this.left())?;
                let right = self.flatten_formula(this.right())?;
                Ok(left.and(right))
            }
            FOF::Or(this) => {
                let left = self.flatten_formula(this.left())?;
                let right = self.flatten_formula(this.right())?;
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
        let var = V(self.flattening_generator.generate_next());
        self.generated_variables.push(var.clone());
        var
    }

    // Recursively flattens a term and returns the resulting formula together with a placeholder variable
    // for the term. Nothing needs to be done if the input term is a variable.
    fn flatten_term(&mut self, term: &Term) -> Option<(FOF, V)> {
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
                        self.flatten_term(t)
                            .map(|(fmla, var)| {
                                conjuncts.push(fmla);
                                var.into()
                            })
                            .unwrap_or_else(|| t.clone())
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
    fn simplify_equations(&self, formula: &FOF) -> FOF {
        let mut map = HashMap::new();
        self.equation_rewrites(formula, &mut map);

        use super::substitution::TermBased;
        let sub = |v: &V| {
            let variable = map.get(v).map(|&t| t.clone()).unwrap_or_else(|| v.clone());
            Term::Var { variable }
        };
        formula.substitute(&sub)
    }

    // As a helper for `simplify_equations` collects a set of rewrite rules as entries of a map, corresponding
    // to equations with an existential variable on one side.
    fn equation_rewrites<'a>(&self, formula: &'a FOF, map: &mut HashMap<&'a V, &'a V>) {
        match formula {
            FOF::Atom(this) => {
                let terms = this.terms();
                if this.predicate().0 == self.equality_symbol {
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
            FOF::Not(this) => {
                self.equation_rewrites(this.formula(), map);
            }
            FOF::And(this) => {
                self.equation_rewrites(this.left(), map);
                self.equation_rewrites(this.right(), map);
            }
            FOF::Or(this) => {
                self.equation_rewrites(this.left(), map);
                self.equation_rewrites(this.right(), map);
            }
            FOF::Implies(this) => {
                self.equation_rewrites(this.premise(), map);
                self.equation_rewrites(this.consequence(), map);
            }
            FOF::Iff(this) => {
                self.equation_rewrites(this.left(), map);
                self.equation_rewrites(this.right(), map);
            }
            FOF::Exists(this) => {
                self.equation_rewrites(this.formula(), map);
            }
            FOF::Forall(this) => {
                self.equation_rewrites(this.formula(), map);
            }
            _ => {}
        }
    }
}

impl Default for Relationalizer {
    /// Creates a new `Relationalizer` instance with default generators and symbols:
    ///   * The equality symbol is `=`.
    ///   * Variables introduced by flattening are prefixed with `?`.
    ///   * Function predicates are prefixed with `$`.    
    fn default() -> Self {
        Self {
            equality_symbol: "=".into(),
            flattening_generator: Generator::new().set_prefix("?"),
            function_predicate_generator: Generator::new().set_prefix("$"),
            constant_predicate_generator: Generator::new().set_prefix("@"),
            generated_variables: Vec::new(),
        }
    }
}

/// Is used to expand implicit equations by replacing variables that appear in more than
/// one position of a formula with freshly generated variables. The expansion algorithm
/// is provided by the [`transform`] method.
///
/// [`transform`]: EqualityExpander::transform()
pub struct EqualityExpander {
    // Is the symbol used to convert equality to a predicate.
    equality_symbol: String,

    // Is the [`Generator`] instance used to generate new variable names when variables
    // appear in more than one position.
    equality_generator: Generator,
}

impl EqualityExpander {
    /// Use `symbol` for equality predicates.
    pub fn set_equality_symbol<S: Into<String>>(&mut self, symbol: S) {
        self.equality_symbol = symbol.into();
    }

    /// Use `generator` to distinguish variables that appear in more than one positions.
    pub fn set_equality_generator(&mut self, generator: Generator) {
        self.equality_generator = generator;
    }

    fn helper(&self, formula: &FOF, vars: &mut HashMap<V, i32>) -> Result<FOF, Error> {
        match formula {
            FOF::Top | FOF::Bottom => Ok(formula.clone()),
            FOF::Atom(this) => {
                let mut equations = Vec::new();
                let mut new_terms = Vec::<Term>::new();
                for term in this.terms() {
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
                    .fold(this.predicate().clone().app(new_terms), |fmla, eq| {
                        fmla.and(eq)
                    }))
            }
            FOF::And(this) => {
                let left = self.helper(this.left(), vars)?;
                let right = self.helper(this.right(), vars)?;
                Ok(left.and(right))
            }
            FOF::Or(this) => {
                let left = self.helper(this.left(), vars)?;
                let right = self.helper(this.right(), vars)?;
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
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::relationalize::{Relationalizer, EqualityExpander};
    ///
    /// let fmla = "P(f(x)) & Q('c)".parse::<FOF>().unwrap();
    /// let relational = Relationalizer::default().transform(&fmla).unwrap();
    /// let transformed = EqualityExpander::default().transform(&relational).unwrap();
    /// assert_eq!(
    ///     r"($f(x, ?0) ∧ (P(~?0:0) ∧ =(?0, ~?0:0))) ∧ (@c(?1) ∧ (Q(~?1:0) ∧ =(?1, ~?1:0)))",
    ///     transformed.formula().to_string()
    /// );
    ///
    /// let fmla = "~P(x)".parse::<FOF>().unwrap();
    /// assert!(Relationalizer::default().transform(&fmla).is_err());
    /// ```
    pub fn transform(&self, formula: &Relational) -> Result<Relational, Error> {
        let transformed = self.helper(formula.formula(), &mut HashMap::new());
        transformed.map(|t| {
            let result = remove_reflexive_equations(&t, &self.equality_symbol);
            Relational(result.unwrap_or(FOF::Top))
        })
    }
}

impl Default for EqualityExpander {
    /// Creates a new `EqualityExpander` instance with default generators and symbols:
    /// * The equality symbol is `=`.
    /// * Variables appearing in more than one position are distinguished with `~` as the
    /// prefix, followed by `:` and a unique index.
    fn default() -> Self {
        Self {
            equality_symbol: "=".into(),
            equality_generator: Generator::new().set_prefix("~").set_delimiter(":"),
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
/// use razor_fol::syntax::FOF;
/// use razor_fol::v;
/// use razor_fol::transform::relationalize::{Relationalizer, range_restrict};
///
/// let fmla = "P(x) & Q(y)".parse::<FOF>().unwrap();
/// let relational = Relationalizer::default().transform(&fmla).unwrap();
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
fn rr_helper(formula: &FOF, range: &[V], symbol: &str) -> Result<FOF, Error> {
    let formula = match formula {
        FOF::Bottom => formula.clone(),
        FOF::Top => rr_conjunct(range, symbol).unwrap_or_else(|| formula.clone()),
        FOF::Atom { .. } | FOF::And { .. } => {
            let free = formula.free_vars();
            let mut range = Vec::from(range);
            range.retain(|x| !free.contains(&x));
            rr_conjunct(&range, symbol)
                .map(|c| formula.clone().and(c))
                .unwrap_or_else(|| formula.clone())
        }
        FOF::Or(this) => {
            let left = rr_helper(this.left(), range, symbol)?;
            let right = rr_helper(this.right(), range, symbol)?;
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
fn rr_conjunct(range: &[V], symbol: &str) -> Option<FOF> {
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

fn combine_binary<F>(first: Option<FOF>, second: Option<FOF>, f: F) -> Option<FOF>
where
    F: FnOnce(FOF, FOF) -> FOF,
{
    match (&first, &second) {
        (None, None) => None,
        (None, Some(_)) => second,
        (Some(_), None) => first,
        (Some(_), Some(_)) => Some(f(first.unwrap(), second.unwrap())),
    }
}

fn remove_reflexive_equations(formula: &FOF, eq_symbol: &str) -> Option<FOF> {
    use crate::syntax::{exists, forall, not};
    match &formula {
        FOF::Atom(this) => {
            let terms = this.terms();
            if this.predicate().0 == eq_symbol {
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
        FOF::Equals(this) => {
            if this.left() == this.right() {
                None
            } else {
                Some(formula.clone())
            }
        }
        FOF::Not(this) => remove_reflexive_equations(this.formula(), eq_symbol).map(not),
        FOF::And(this) => combine_binary(
            remove_reflexive_equations(this.left(), eq_symbol),
            remove_reflexive_equations(this.right(), eq_symbol),
            FOF::and,
        ),
        FOF::Or(this) => combine_binary(
            remove_reflexive_equations(this.left(), eq_symbol),
            remove_reflexive_equations(this.right(), eq_symbol),
            FOF::or,
        ),
        FOF::Implies(this) => combine_binary(
            remove_reflexive_equations(this.premise(), eq_symbol),
            remove_reflexive_equations(this.consequence(), eq_symbol),
            FOF::implies,
        ),
        FOF::Iff(this) => combine_binary(
            remove_reflexive_equations(this.left(), eq_symbol),
            remove_reflexive_equations(this.right(), eq_symbol),
            FOF::iff,
        ),
        FOF::Exists(this) => remove_reflexive_equations(this.formula(), eq_symbol)
            .map(|f| exists(this.variables().to_vec(), f)),
        FOF::Forall(this) => remove_reflexive_equations(this.formula(), eq_symbol)
            .map(|f| forall(this.variables().to_vec(), f)),
        _ => Some(formula.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{fof, v};

    #[test]
    fn test_relationalize_formula() -> Result<(), Error> {
        assert_eq! {
            "⊤",
            Relationalizer::default().flatten_formula(&fof!('|'))?.to_string(),
        };
        assert_eq! {
            "⟘",
            Relationalizer::default().flatten_formula(&fof!(_|_))?.to_string(),
        };
        assert_eq! {
            "P()",
            Relationalizer::default().flatten_formula(&fof!(P()))?.to_string(),
        };
        assert_eq! {
            "P(x, y)",
            Relationalizer::default().flatten_formula(&fof!(P(x, y)))?.to_string(),
        };
        assert_eq! {
            "=(x, y)",
            Relationalizer::default().flatten_formula(&fof!((x) = (y)))?.to_string(),
        }
        assert_eq! {
            r"@c(?0) ∧ =(x, ?0)",
            Relationalizer::default().flatten_formula(&fof!((x) = (@c)))?.to_string(),
        }
        assert_eq! {
            r"(@c(?0) ∧ @d(?1)) ∧ =(?0, ?1)",
            Relationalizer::default().flatten_formula(&fof!((@c) = (@d)))?.to_string(),
        }
        assert_eq! {
            r"@c(?0) ∧ P(?0)",
            Relationalizer::default().flatten_formula(&fof!(P(@c)))?.to_string(),
        };
        assert_eq! {
            r"@c(?0) ∧ P(x, ?0)",
            Relationalizer::default().flatten_formula(&fof!(P(x, @c)))?.to_string(),
        };
        assert_eq! {
            r"(@c(?0) ∧ @d(?1)) ∧ P(?0, ?1)",
            Relationalizer::default().flatten_formula(&fof!(P(@c, @d)))?.to_string(),
        };
        assert_eq! {
            r"$f(x, ?0) ∧ P(?0)",
            Relationalizer::default().flatten_formula(&fof!(P(f(x))))?.to_string(),
        };
        assert_eq! {
            "($g(x, ?0) ∧ $f(?0, ?1)) ∧ P(?1)",
            Relationalizer::default().flatten_formula(&fof!(P(f(g(x)))))?.to_string(),
        };
        assert_eq! {
            "(($g(x, ?0) ∧ $f(?0, ?1)) ∧ $f(y, ?2)) ∧ P(?1, ?2)",
            Relationalizer::default().flatten_formula(&fof!(P(f(g(x)), f(y))))?.to_string(),
        };
        assert_eq! {
            "P(x) ∧ Q(y)",
            Relationalizer::default().flatten_formula(&fof!((P(x)) & (Q(y))))?.to_string(),
        };
        assert_eq! {
            "(@c(?0) ∧ P(?0)) ∧ (@d(?1) ∧ Q(?1))",
            Relationalizer::default().flatten_formula(&fof!((P(@c)) & (Q(@d))))?.to_string(),
        };
        assert_eq! {
            "P(x) ∨ Q(y)",
            Relationalizer::default().flatten_formula(&fof!((P(x)) | (Q(y))))?.to_string(),
        };
        assert_eq! {
            "(@c(?0) ∧ P(?0)) ∨ (@d(?1) ∧ Q(?1))",
            Relationalizer::default().flatten_formula(&fof!((P(@c)) | (Q(@d))))?.to_string(),
        };

        assert!(Relationalizer::default()
            .flatten_formula(&fof!(~[P()]))
            .is_err());
        assert!(Relationalizer::default()
            .flatten_formula(&fof!([P()] -> [Q()]))
            .is_err());
        assert!(Relationalizer::default()
            .flatten_formula(&fof!([P()] <=> [Q()]))
            .is_err());
        assert!(Relationalizer::default()
            .flatten_formula(&fof!(?x.[P(x)]))
            .is_err());
        assert!(Relationalizer::default()
            .flatten_formula(&fof!(!x.[P(x)]))
            .is_err());

        Ok(())
    }

    #[test]
    fn test_expand_equality() -> Result<(), Error> {
        fn expand_equality(formula: &FOF) -> Result<FOF, Error> {
            EqualityExpander::default().helper(formula, &mut HashMap::new())
        }

        assert_eq!("⊤", expand_equality(&fof!('|'))?.to_string(),);
        assert_eq!("⟘", expand_equality(&fof!(_|_))?.to_string(),);
        assert_eq!("P()", expand_equality(&fof!(P()))?.to_string(),);
        assert_eq!("P(x, y)", expand_equality(&fof!(P(x, y)))?.to_string(),);
        assert_eq!(
            "P(x, ~x:0) ∧ =(x, ~x:0)",
            expand_equality(&fof!(P(x, x)))?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∧ (Q(~x:0) ∧ =(x, ~x:0))",
            expand_equality(&fof!([P(x, y)] & [Q(x)]))?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∧ ((Q(~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            expand_equality(&fof!([P(x, y)] & [Q(x, y)]))?.to_string(),
        );
        assert_eq!(
            "P(x) ∧ ((Q(y, ~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            expand_equality(&fof!([P(x)] & [Q(y, x, y)]))?.to_string(),
        );
        assert_eq!(
            "(P(x) ∧ (Q(~x:0) ∧ =(x, ~x:0))) ∧ (R(~x:1) ∧ =(x, ~x:1))",
            expand_equality(&fof!({ [P(x)] & [Q(x)] } & { R(x) }))?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∨ (Q(~x:0) ∧ =(x, ~x:0))",
            expand_equality(&fof!([P(x, y)] | [Q(x)]))?.to_string(),
        );
        assert_eq!(
            "P(x, y) ∨ ((Q(~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            expand_equality(&fof!([P(x, y)] | [Q(x, y)]))?.to_string(),
        );
        assert_eq!(
            "P(x) ∨ ((Q(y, ~x:0, ~y:0) ∧ =(x, ~x:0)) ∧ =(y, ~y:0))",
            expand_equality(&fof!([P(x)] | [Q(y, x, y)]))?.to_string(),
        );
        assert_eq!(
            "(P(x) ∨ (Q(~x:0) ∧ =(x, ~x:0))) ∨ (R(~x:1) ∧ =(x, ~x:1))",
            expand_equality(&fof!({ [P(x)] | [Q(x)] } | { R(x) }))?.to_string(),
        );

        assert!(expand_equality(&fof!(P(@c))).is_err());
        assert!(expand_equality(&fof!(P(f(x)))).is_err());
        assert!(expand_equality(&fof!(~[P()])).is_err());
        assert!(expand_equality(&fof!([P()] -> [Q()])).is_err());
        assert!(expand_equality(&fof!([P()] <=> [Q()])).is_err());
        assert!(expand_equality(&fof!(?x.[P(x)])).is_err());
        assert!(expand_equality(&fof!(!x.[P(x)])).is_err());

        Ok(())
    }

    #[test]
    fn test_range_restrict() -> Result<(), Error> {
        let rr = "RR";
        assert_eq!("⊤", rr_helper(&fof!('|'), &vec![], rr)?.to_string());
        assert_eq!(
            "RR(x)",
            rr_helper(&fof!('|'), &vec![v!(x)], rr)?.to_string()
        );
        assert_eq!(
            "RR(x) ∧ RR(y)",
            rr_helper(&fof!('|'), &vec![v!(x), v!(y)], rr)?.to_string()
        );
        assert_eq!("⟘", rr_helper(&fof!(_|_), &vec![], rr)?.to_string());

        assert_eq!("P(x)", rr_helper(&fof!(P(x)), &vec![], rr)?.to_string());
        assert_eq!(
            "P(w, x, y) ∧ RR(z)",
            rr_helper(&fof!(P(w, x, y)), &vec![v!(x), v!(y), v!(z)], rr)?.to_string()
        );

        assert_eq!(
            "P(x) ∧ Q(y)",
            rr_helper(&fof!([P(x)] & [Q(y)]), &vec![], rr)?.to_string()
        );
        assert_eq!(
            "(P(v, w) ∧ Q(x)) ∧ (RR(y) ∧ RR(z))",
            rr_helper(
                &fof!([P(v, w)] & [Q(x)]),
                &vec![v!(v), v!(w), v!(x), v!(y), v!(z)],
                rr
            )?
            .to_string()
        );

        assert_eq!(
            "P(x) ∨ Q(y)",
            rr_helper(&fof!([P(x)] | [Q(y)]), &vec![], rr)?.to_string()
        );

        assert_eq!(
            "(P(x) ∧ RR(y)) ∨ (Q(y) ∧ RR(x))",
            rr_helper(&fof!([P(x)] | [Q(y)]), &vec![v!(x), v!(y)], rr)?.to_string()
        );

        Ok(())
    }

    #[test]
    fn test_relationalize() -> Result<(), Error> {
        assert_eq!(
            "$f(x, y)",
            Relationalizer::default()
                .transform(&fof!([f(x)] = [y]))?
                .formula()
                .to_string()
        );
        assert_eq!(
            "$f(x, ?1) ∧ $g(y, ?1)",
            Relationalizer::default()
                .transform(&fof!([f(x)] = [g(y)]))?
                .formula()
                .to_string()
        );
        assert_eq!(
            "($f(x, ?1) ∧ $g(y, ?1)) ∨ $f(x, y)",
            Relationalizer::default()
                .transform(&fof!({ [f(x)] = [g(y)] } | { [f(x)] = [y] }))?
                .formula()
                .to_string()
        );
        assert_eq!(
            "$f(y, ?0) ∧ P(x, ?0)",
            Relationalizer::default()
                .transform(&fof!(P(x, f(y))))?
                .formula()
                .to_string()
        );
        assert_eq!(
            "$f(x, ?0) ∧ P(x, ?0)",
            Relationalizer::default()
                .transform(&fof!(P(x, f(x))))?
                .formula()
                .to_string()
        );

        Ok(())
    }
}
