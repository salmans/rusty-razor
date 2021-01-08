/*! Implements a relationalization algorithm for formulae.*/
use super::PcfSet;
use crate::syntax::{
    formula::*,
    symbol::Generator,
    term::Complex,
    term::{Renaming, Substitution},
    Error, Formula, Pred, Sig, Term, FOF, V,
};
use itertools::Itertools;
use std::{collections::HashMap, ops::Deref};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct Variable(V);

impl Variable {
    /// Returns the variable symbol of this variable.
    #[inline(always)]
    pub fn symbol(&self) -> &V {
        &self.0
    }
}

impl Deref for Variable {
    type Target = V;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<V> for Variable {
    fn from(value: V) -> Self {
        Self(value)
    }
}

type FlatAtom = Atomic<Variable>;

impl Term for Variable {
    fn signature(&self) -> Result<Sig, Error> {
        Ok(Sig::new())
    }

    fn vars(&self) -> Vec<&V> {
        vec![&self.0]
    }

    fn transform(&self, f: &impl Fn(&Self) -> Self) -> Self {
        f(self)
    }

    fn rename_vars(&self, renaming: &impl Renaming) -> Self {
        renaming.apply(&self.0).clone().into()
    }

    fn substitute(&self, sub: &impl Substitution<Self>) -> Self {
        sub.apply(&self.0).into()
    }
}

#[derive(Clone, Debug)]
pub struct RelClause(Vec<FlatAtom>);

impl RelClause {
    /// Returns the list of atomic formulae of the receiver clause.
    pub fn atomics(&self) -> &[FlatAtom] {
        &self.0
    }

    /// Consumes the receiver and returns its underlying list of [`Atomic`]s.
    pub fn into_atomics(self) -> Vec<FlatAtom> {
        self.0
    }
}

impl Deref for RelClause {
    type Target = [FlatAtom];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<FlatAtom> for RelClause {
    fn from(value: FlatAtom) -> Self {
        Self(vec![value])
    }
}

impl<I> From<I> for RelClause
where
    I: IntoIterator<Item = FlatAtom>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Default for RelClause {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl Formula for RelClause {
    type Term = Variable;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|l| l.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&V> {
        let mut vs = Vec::new();
        for lit in &self.0 {
            vs.extend(lit.free_vars());
        }
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Variable) -> Variable) -> Self {
        self.0.iter().map(|lit| lit.transform(f)).into()
    }
}

impl From<FlatAtom> for FOF {
    fn from(value: FlatAtom) -> Self {
        match value {
            Atomic::Atom(this) => Atom::<Complex> {
                predicate: this.predicate,
                terms: this.terms.into_iter().map(|v| v.symbol().into()).collect(),
            }
            .into(),
            Atomic::Equals(this) => Equals {
                left: this.left.symbol().into(),
                right: this.right.symbol().into(),
            }
            .into(),
        }
    }
}

impl From<RelClause> for FOF {
    fn from(value: RelClause) -> Self {
        value
            .into_atomics()
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

/// Represents a relational formula as a Disjunctive Normal Form (DNF) over positive atomic
/// formulae with flat terms. In Razor, the primary use-case of this type is to
/// transform positive formulae in the head and body of a [`GNF`] to relational forms.
///
/// **Hint**: A relationalized formula contains only (flat) variable terms with
/// no function symbol nor constants.
///
/// [`GNF`]: crate::transform::GNF
#[derive(Clone, Debug)]
pub struct Relational(Vec<RelClause>);

impl From<RelClause> for Relational {
    fn from(value: RelClause) -> Self {
        vec![value].into_iter().into()
    }
}

impl<I> From<I> for Relational
where
    I: IntoIterator<Item = RelClause>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Relational {
    pub fn clauses(&self) -> &[RelClause] {
        &self.0
    }

    pub fn into_clauses(self) -> Vec<RelClause> {
        self.0
    }
}

impl Deref for Relational {
    type Target = [RelClause];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Default for Relational {
    fn default() -> Self {
        Vec::<RelClause>::new().into()
    }
}

impl Formula for Relational {
    type Term = Variable;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&V> {
        let mut vs = Vec::new();
        for clause in &self.0 {
            vs.extend(clause.free_vars());
        }
        vs.into_iter().unique().collect()
    }

    fn transform(&self, f: &impl Fn(&Variable) -> Variable) -> Self {
        self.0.iter().map(|clause| clause.transform(f)).into()
    }
}

impl From<Relational> for FOF {
    fn from(value: Relational) -> Self {
        value
            .into_clauses()
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
    }
}

impl From<&Relational> for FOF {
    fn from(value: &Relational) -> Self {
        value.clone().into()
    }
}

impl std::fmt::Display for Relational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

/// Provides the relationalization algorithm through the [`transform`] method.
///
/// [`transform`]: Relational::transform()
pub struct RelationalConfig {
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

impl RelationalConfig {
    /// Use `generator` to generate flattening variable names.
    pub fn set_flattening_generator(&mut self, generator: Generator) {
        self.flattening_generator = generator;
    }

    /// Use `generator` to create function predicate names.
    pub fn set_predicate_generator(&mut self, generator: Generator) {
        self.function_predicate_generator = generator;
    }

    // Generates a new variable using the `flattening_generator` and keeps track of it in
    // `generated_variables`.
    fn generate_variable(&mut self) -> V {
        let var = V(self.flattening_generator.generate_next());
        self.generated_variables.push(var.clone());
        var
    }
}

impl Default for RelationalConfig {
    /// Creates a new `RelationalConfig` instance with default generators and symbols:
    ///   * The equality symbol is `=`.
    ///   * Variables introduced by flattening are prefixed with `?`.
    ///   * Function predicates are prefixed with `$`.    
    fn default() -> Self {
        Self {
            flattening_generator: Generator::new().set_prefix("?"),
            function_predicate_generator: Generator::new().set_prefix("$"),
            constant_predicate_generator: Generator::new().set_prefix("@"),
            generated_variables: Vec::new(),
        }
    }
}

// Recursively flattens a term and returns the resulting formula together with a placeholder variable
// for the term. Nothing needs to be done if the input term is a variable.
fn flatten_term(term: &Complex, relationalizer: &mut RelationalConfig) -> (Option<RelClause>, V) {
    match term {
        Complex::Var { variable } => (None, variable.clone()),
        Complex::Const { constant } => {
            let var = relationalizer.generate_variable();
            let terms = vec![var.clone().into()];
            let predicate = Pred(
                relationalizer
                    .constant_predicate_generator
                    .symbol(constant.0.to_string()),
            );
            let atom = Atom { predicate, terms };
            (Some(vec![atom.into()].into()), var)
        }
        Complex::App { function, terms } => {
            let mut conjuncts = vec![];
            let mut terms = terms
                .iter()
                .map(|t| {
                    let (clauses, var) = flatten_term(t, relationalizer);
                    if let Some(cs) = clauses {
                        conjuncts.extend(cs.into_atomics());
                    }
                    var.into()
                })
                .collect::<Vec<Variable>>();

            let var = relationalizer.generate_variable();
            terms.push(var.clone().into());

            let predicate = Pred(
                relationalizer
                    .function_predicate_generator
                    .symbol(function.0.to_string()),
            );
            let atom = Atom { predicate, terms };

            // !!! This is preserving the topological order among variables:
            conjuncts.push(atom.into());
            (Some(conjuncts.into()), var)
        }
    }
}

// Applies top level flattening on the input formula.
fn flatten_formula(clause_set: &PcfSet, relationalizer: &mut RelationalConfig) -> Relational {
    clause_set
        .iter()
        .map(|clause| {
            clause
                .iter()
                .flat_map(|lit| match lit {
                    Atomic::Atom(this) => {
                        let mut conjuncts = Vec::new();
                        let terms = this
                            .terms
                            .iter()
                            .map(|t| {
                                let (clauses, var) = flatten_term(t, relationalizer);
                                if let Some(cs) = clauses {
                                    conjuncts.extend(cs.into_atomics());
                                }
                                var.into()
                            })
                            .collect::<Vec<Variable>>();

                        let atom = Atom {
                            predicate: this.predicate.clone(),
                            terms,
                        }
                        .into();

                        // !!! Preserving the topological order among variables:
                        conjuncts.push(atom);
                        conjuncts
                    }
                    Atomic::Equals(this) => {
                        let mut conjuncts = vec![];
                        let (left_clauses, left_var) = flatten_term(&this.left, relationalizer);
                        if let Some(cs) = left_clauses {
                            conjuncts.extend(cs.into_atomics());
                        }
                        let left = left_var.into();

                        let (right_clauses, right_var) = flatten_term(&this.right, relationalizer);
                        if let Some(cs) = right_clauses {
                            conjuncts.extend(cs.into_atomics());
                        }
                        let right = right_var.into();
                        let equals = Equals { left, right }.into();

                        conjuncts.push(equals);
                        conjuncts
                    }
                })
                .into()
        })
        .into()
}

// As a helper for `simplify_equations` collects a set of rewrite rules as entries of a map, corresponding
// to equations with an existential variable on one side.
fn equation_rewrites<'a>(
    clause_set: &'a Relational,
    map: &mut HashMap<&'a V, &'a V>,
    relationalizer: &mut RelationalConfig,
) {
    clause_set.iter().for_each(|clause| {
        clause.iter().for_each(|atomic| match atomic {
            Atomic::Equals(this) => {
                let left = &this.left;
                let right = &this.right;

                let l_generated = relationalizer.generated_variables.contains(left.symbol());
                let r_generated = relationalizer.generated_variables.contains(right.symbol());

                match (l_generated, r_generated) {
                    (false, true) => {
                        map.insert(right, left);
                    }
                    (true, false) => {
                        map.insert(left, right);
                    }
                    (true, true) => {
                        if map.contains_key(left.symbol()) {
                            map.insert(right, map.get(left.symbol()).unwrap());
                        } else if map.contains_key(right.symbol()) {
                            map.insert(left, map.get(right.symbol()).unwrap());
                        } else {
                            map.insert(left, right);
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        });
    });
}

// Simplify tries to minimize the use of existential variables (generated by relationalize) by replacing
// them with universal or other existential variables that are syntactically equal with them.
fn simplify_equations(
    clause_set: &Relational,
    relationalizer: &mut RelationalConfig,
) -> Relational {
    let mut map = HashMap::new();
    equation_rewrites(clause_set, &mut map, relationalizer);

    let sub = |v: &V| {
        let variable = map.get(v).map(|&t| t.clone()).unwrap_or_else(|| v.clone());
        Variable(variable)
    };
    clause_set.substitute(&sub)
}

impl PcfSet {
    /// Is similar to [`PcfSet::relational`] but uses a custom [`RelationalConfig`].
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::RelationalConfig;
    ///
    /// let fof = "P(x) -> P(f(x)) & Q('c)".parse::<FOF>().unwrap();
    /// let gnfs = fof.gnf();
    /// let gnf_head = gnfs[0].head();
    /// let transformed = gnf_head.relational();
    /// assert_eq!(
    ///     r"(($f(x, ?0) ∧ P(?0)) ∧ @c(?1)) ∧ Q(?1)",
    ///     transformed.to_string()
    /// );
    /// ```
    pub fn relational_with(&self, relationalizer: &mut RelationalConfig) -> Relational {
        let flattened = flatten_formula(self, relationalizer);
        let simplified = simplify_equations(&flattened, relationalizer);
        simplified
            .into_clauses()
            .into_iter()
            .map(|clause| {
                clause
                    .into_atomics()
                    .into_iter()
                    // remove reflexive equations:
                    .filter(|atomic| match atomic {
                        Atomic::Equals(this) => this.left != this.right,
                        _ => true,
                    })
                    .into()
            })
            .into()
    }

    /// Applies the relationalization algorithm on the receiver and returns a relational formula.    
    ///
    /// **Note:**
    /// The underlying algorithm works on input first-order formulae that are negation and quantifier-free:
    /// `¬`, `→`, `⇔`, `∃`, `∀` are not allowed as connectives. This requirement is satisfied by an instance
    /// of PcfSet, which represents a Disjunctive Normal Form over positive literals.
    /// Relationalization consists of applying the following rewrites on the input formula:
    ///   * A constant `'c` rewrites to a predicate `C(x)`.
    ///   * A complex term `f(x_1, ..., x_n)` rewrites to a fresh variable `v` and an atomic
    /// formula `F(x_1, ..., x_n, v)` is conjoined with the input formula.
    ///   * An equation `v = y` rewrites to an atomic formula `=(x, y)`.
    ///
    /// In the resulting formula, the new (placeholder) variables are sorted topologically from
    /// left to right where the ordering relation is the dependency between the new variables.
    /// A varialbe `v` depends on a variable `y` if and only if for a new function predicate, namely `F`,
    /// `F(..., y,..., v)` is a conjunct in the formula (i.e., the result of the
    /// function replaced by `F`, applied to its arguments, depends on `y`).
    ///
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::RelationalConfig;
    ///
    /// let fof = "P(x) -> P(f(x)) & Q('c)".parse::<FOF>().unwrap();
    /// let gnfs = fof.gnf();
    /// let gnf_head = gnfs[0].head();
    /// let transformed = gnf_head.relational();
    /// assert_eq!(
    ///     r"(($f(x, ?0) ∧ P(?0)) ∧ @c(?1)) ∧ Q(?1)",
    ///     transformed.to_string()
    /// );
    /// ```
    pub fn relational(&self) -> Relational {
        self.relational_with(&mut RelationalConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{fof, transform::PCF};

    // Assumes the input in GNF
    fn clause_set(fof: FOF) -> Vec<PcfSet> {
        fof.gnf()
            .into_iter()
            .map(|f| f.into_body_and_head().1)
            .collect()
    }

    fn flatten(fof: FOF) -> String {
        let rels = clause_set(fof)
            .iter()
            .map(|f| flatten_formula(f, &mut RelationalConfig::default()))
            .map(FOF::from)
            .collect::<Vec<_>>();
        format!("{:?}", rels)
    }

    #[test]
    fn test_flatten() {
        assert_eq! {
            "[]",
            flatten(fof!('|')),
        };

        assert_eq! {
            "[false]",
            flatten(fof!(_|_)),
        };

        assert_eq! {
            "[P()]",
            flatten(fof!(P())),
        };
        assert_eq! {
            "[P(x, y)]",
            flatten(fof!(P(x, y))),
        };
        assert_eq! {
            "[x = y]",
            flatten(fof!((x) = (y))),
        }

        assert_eq! {
            "[@c(?0) & (x = ?0)]",
            flatten(fof!((x) = (@c))),
        }
        assert_eq! {
            "[(@c(?0) & @d(?1)) & (?0 = ?1)]",
            flatten(fof!((@c) = (@d))),
        }
        assert_eq! {
            "[@c(?0) & P(?0)]",
            flatten(fof!(P(@c))),
        };
        assert_eq! {
            "[@c(?0) & P(x, ?0)]",
            flatten(fof!(P(x, @c))),
        };
        assert_eq! {
            "[(@c(?0) & @d(?1)) & P(?0, ?1)]",
            flatten(fof!(P(@c, @d))),
        };
        assert_eq! {
            "[$f(x, ?0) & P(?0)]",
            flatten(fof!(P(f(x)))),
        };
        assert_eq! {
            "[($g(x, ?0) & $f(?0, ?1)) & P(?1)]",
            flatten(fof!(P(f(g(x))))),
        };
        assert_eq! {
            "[(($g(x, ?0) & $f(?0, ?1)) & $f(y, ?2)) & P(?1, ?2)]",
            flatten(fof!(P(f(g(x)), f(y)))),
        };
        assert_eq! {
            "[P(x), Q(y)]",
            flatten(fof!((P(x)) & (Q(y)))),
        };
        assert_eq! {
            "[((@c(?0) & P(?0)) & @d(?1)) & Q(?1)]",
            flatten(fof!((P(@c)) & (Q(@d)))),
        };
        assert_eq! {
            "[P(x) | Q(y)]",
            flatten(fof!((P(x)) | (Q(y)))),
        };
        assert_eq! {
            "[(@c(?0) & P(?0)) | (@d(?1) & Q(?1))]",
            flatten(fof!((P(@c)) | (Q(@d)))),
        };
    }

    #[test]
    fn test_relationalize() {
        use crate::{syntax::formula::*, term};
        {
            let clause_set = PcfSet::from(vec![PCF::from(Equals {
                left: term!(f(x)),
                right: term!(y),
            })]);
            assert_eq!("$f(x, y)", clause_set.relational().to_string());
        }
        {
            let clause_set = PcfSet::from(vec![PCF::from(Equals {
                left: term!(f(x)),
                right: term!(g(y)),
            })]);
            assert_eq!("$f(x, ?1) ∧ $g(y, ?1)", clause_set.relational().to_string());
        }
        {
            let clause_set = PcfSet::from(vec![
                PCF::from(Equals {
                    left: term!(f(x)),
                    right: term!(g(y)),
                }),
                PCF::from(Equals {
                    left: term!(f(x)),
                    right: term!(y),
                }),
            ]);
            assert_eq!(
                "$f(x, y) ∨ ($f(x, ?2) ∧ $g(y, ?2))",
                clause_set.relational().to_string()
            );
        }
        {
            let clause_set = PcfSet::from(vec![PCF::from(Atom {
                predicate: Pred::from("P"),
                terms: vec![term!(x), term!(f(y))],
            })]);
            assert_eq!("$f(y, ?0) ∧ P(x, ?0)", clause_set.relational().to_string());
        }
        {
            let clause_set = PcfSet::from(vec![PCF::from(Atom {
                predicate: Pred::from("P"),
                terms: vec![term!(x), term!(f(x))],
            })]);
            assert_eq!("$f(x, ?0) ∧ P(x, ?0)", clause_set.relational().to_string());
        }
    }
}
