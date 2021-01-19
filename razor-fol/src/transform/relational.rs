/*! Implements a relationalization algorithm for formulae.*/
use super::{PCFSet, PCF};
use crate::syntax::{
    formula::*,
    term::{Complex, Variable},
    Const, Error, Formula, Func, Pred, Sig, Var, FOF,
};
use itertools::Itertools;
use std::{collections::HashMap, ops::Deref};

type FlatAtom = Atomic<Variable>;

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
        Sig::from_signatures(
            self.iter()
                .map(|l| l.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
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

pub trait ToRelational: Formula {
    /// Is similar to [`PCFSet::relational`] but uses custom closures for generating symbols.
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{FOF, Const, Var, Func};
    /// use razor_fol::transform::{ToGNF, ToRelational};
    ///
    /// let fof = "P(x) -> P(f(x)) & Q('c)".parse::<FOF>().unwrap();
    /// let gnfs = fof.gnf();
    /// let gnf_head = gnfs[0].head();
    /// let mut var_counter = 0;
    /// let mut var_generator = || {
    ///    let name = var_counter.to_string();
    ///    var_counter += 1;
    ///    name.into()
    /// };
    /// let mut const_generator = |c: &Const| c.name().to_uppercase().into();
    /// let mut fn_generator = |f: &Func| f.name().to_uppercase().into();    
    /// let transformed = gnf_head.relational_with(&mut var_generator, &mut const_generator, &mut fn_generator);
    /// assert_eq!(
    ///     r"((F(x, 0) ∧ P(0)) ∧ C(1)) ∧ Q(1)",
    ///     transformed.to_string()
    /// );
    /// ```
    fn relational_with<VG, CG, FG>(
        &self,
        var_generator: &mut VG,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Relational
    where
        VG: FnMut() -> Var,
        CG: FnMut(&Const) -> Pred,
        FG: FnMut(&Func) -> Pred;

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
    /// use razor_fol::transform::{ToGNF, ToRelational};
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
    fn relational(&self) -> Relational {
        let mut var_counter = 0;
        let mut var_generator = || {
            let name = format!("?{}", var_counter);
            var_counter += 1;
            name.into()
        };
        let mut const_generator = |c: &Const| format!("@{}", c.name()).into();
        let mut fn_generator = |f: &Func| format!("${}", f.name()).into();

        self.relational_with(&mut var_generator, &mut const_generator, &mut fn_generator)
    }
}

impl ToRelational for PCF {
    fn relational_with<VG, CG, FG>(
        &self,
        var_generator: &mut VG,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Relational
    where
        VG: FnMut() -> Var,
        CG: FnMut(&Const) -> Pred,
        FG: FnMut(&Func) -> Pred,
    {
        // keeping track of the generated variables to remove reflexive equations later on:
        let mut generated_vars = Vec::new();
        let mut var_generator_ex = || {
            let v = var_generator();
            generated_vars.push(v.clone());
            v
        };
        let flattened = flatten_clause(self, &mut var_generator_ex, const_generator, fn_generator);
        let relational: Relational = flattened.into();
        let simplified = simplify_equations(&relational, &mut generated_vars);

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
}

impl ToRelational for PCFSet {
    fn relational_with<VG, CG, FG>(
        &self,
        var_generator: &mut VG,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Relational
    where
        VG: FnMut() -> Var,
        CG: FnMut(&Const) -> Pred,
        FG: FnMut(&Func) -> Pred,
    {
        // keeping track of the generated variables to remove reflexive equations later on:
        let mut generated_vars = Vec::new();
        let mut var_generator_ex = || {
            let v = var_generator();
            generated_vars.push(v.clone());
            v
        };
        let flattened =
            flatten_clause_set(self, &mut var_generator_ex, const_generator, fn_generator);
        let simplified = simplify_equations(&flattened, &mut generated_vars);

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
}

impl Formula for Relational {
    type Term = Variable;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
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

// Recursively flattens a term and returns the resulting formula together with a placeholder variable
// for the term. Nothing needs to be done if the input term is a variable.
fn flatten_term<VG, CG, FG>(
    term: &Complex,
    var_generator: &mut VG,
    const_generator: &mut CG,
    fn_generator: &mut FG,
) -> (Option<RelClause>, Var)
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    match term {
        Complex::Var { variable } => (None, variable.clone()),
        Complex::Const { constant } => {
            let var = var_generator();
            let terms = vec![var.clone().into()];
            let predicate = const_generator(constant);
            let atom = Atom { predicate, terms };
            (Some(vec![atom.into()].into()), var)
        }
        Complex::App { function, terms } => {
            let mut conjuncts = vec![];
            let mut terms = terms
                .iter()
                .map(|t| {
                    let (clauses, var) =
                        flatten_term(t, var_generator, const_generator, fn_generator);
                    if let Some(cs) = clauses {
                        conjuncts.extend(cs.into_atomics());
                    }
                    var.into()
                })
                .collect::<Vec<Variable>>();

            let var = var_generator();
            terms.push(var.clone().into());

            let predicate = fn_generator(function);
            let atom = Atom { predicate, terms };

            // !!! This is preserving the topological order among variables:
            conjuncts.push(atom.into());
            (Some(conjuncts.into()), var)
        }
    }
}

// Applies top level flattening on the input clause set of type `PCFSet`.
fn flatten_clause_set<VG, CG, FG>(
    clause_set: &PCFSet,
    var_generator: &mut VG,
    const_generator: &mut CG,
    fn_generator: &mut FG,
) -> Relational
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    clause_set
        .iter()
        .map(|clause| flatten_clause(clause, var_generator, const_generator, fn_generator))
        .into()
}

// Applies top level flattening on the input clause set.
fn flatten_clause<VG, CG, FG>(
    clause: &PCF,
    var_generator: &mut VG,
    const_generator: &mut CG,
    fn_generator: &mut FG,
) -> RelClause
where
    VG: FnMut() -> Var,
    CG: FnMut(&Const) -> Pred,
    FG: FnMut(&Func) -> Pred,
{
    clause
        .iter()
        .flat_map(|lit| match lit {
            Atomic::Atom(this) => {
                let mut conjuncts = Vec::new();
                let terms = this
                    .terms
                    .iter()
                    .map(|t| {
                        let (clauses, var) =
                            flatten_term(t, var_generator, const_generator, fn_generator);
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
                let (left_clauses, left_var) =
                    flatten_term(&this.left, var_generator, const_generator, fn_generator);
                if let Some(cs) = left_clauses {
                    conjuncts.extend(cs.into_atomics());
                }
                let left = left_var.into();

                let (right_clauses, right_var) =
                    flatten_term(&this.right, var_generator, const_generator, fn_generator);
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
}

// As a helper for `simplify_equations` collects a set of rewrite rules as entries of a map, corresponding
// to equations with an existential variable on one side.
fn equation_rewrites<'a>(
    clause_set: &'a Relational,
    map: &mut HashMap<&'a Var, &'a Var>,
    generated_variables: &mut Vec<Var>,
) {
    clause_set.iter().for_each(|clause| {
        clause.iter().for_each(|atomic| match atomic {
            Atomic::Equals(this) => {
                let left = &this.left;
                let right = &this.right;

                let l_generated = generated_variables.contains(left.symbol());
                let r_generated = generated_variables.contains(right.symbol());

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
fn simplify_equations(clause_set: &Relational, generated_variables: &mut Vec<Var>) -> Relational {
    let mut map = HashMap::new();
    equation_rewrites(clause_set, &mut map, generated_variables);

    let sub = |v: &Var| {
        let variable = map.get(v).map(|&t| t.clone()).unwrap_or_else(|| v.clone());
        Variable::from(variable)
    };
    clause_set.substitute(&sub)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{fof, transform::PCF};

    // Assumes the input in GNF
    fn clause_set(fof: FOF) -> Vec<PCFSet> {
        use crate::transform::ToGNF;

        fof.gnf()
            .into_iter()
            .map(|f| f.into_body_and_head().1)
            .collect()
    }

    fn flatten(fof: FOF) -> String {
        let mut var_counter = 0;
        let mut var_generator = || {
            let name = format!("?{}", var_counter);
            var_counter += 1;
            name.into()
        };
        let mut const_generator = |c: &Const| format!("@{}", c.name()).into();
        let mut fn_generator = |f: &Func| format!("${}", f.name()).into();

        let rels = clause_set(fof)
            .iter()
            .map(|f| {
                flatten_clause_set(
                    f,
                    &mut var_generator,
                    &mut const_generator,
                    &mut fn_generator,
                )
            })
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
            "[@c(?0) & x = ?0]",
            flatten(fof!((x) = (@c))),
        }
        assert_eq! {
            "[(@c(?0) & @d(?1)) & ?0 = ?1]",
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
            let clause_set = PCFSet::from(vec![PCF::from(Equals {
                left: term!(f(x)),
                right: term!(y),
            })]);
            assert_eq!("$f(x, y)", clause_set.relational().to_string());
        }
        {
            let clause_set = PCFSet::from(vec![PCF::from(Equals {
                left: term!(f(x)),
                right: term!(g(y)),
            })]);
            assert_eq!("$f(x, ?1) ∧ $g(y, ?1)", clause_set.relational().to_string());
        }
        {
            let clause_set = PCFSet::from(vec![
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
            let clause_set = PCFSet::from(vec![PCF::from(Atom {
                predicate: Pred::from("P"),
                terms: vec![term!(x), term!(f(y))],
            })]);
            assert_eq!("$f(y, ?0) ∧ P(x, ?0)", clause_set.relational().to_string());
        }
        {
            let clause_set = PCFSet::from(vec![PCF::from(Atom {
                predicate: Pred::from("P"),
                terms: vec![term!(x), term!(f(x))],
            })]);
            assert_eq!("$f(x, ?0) ∧ P(x, ?0)", clause_set.relational().to_string());
        }
    }
}
