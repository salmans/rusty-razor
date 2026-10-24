/*! Defines standard geometric sequents and implements a conversion from first-order formulae
to [`Geometric`] sequents that Skolemizes an existential quantifier only when it must.

A *positive-existential formula* (PEF) is built from atoms, equations, `⊤`, `⊥`, `∧`, `∨` and
`∃`. A *geometric sequent* `φ ⊢x̄ ψ` has a PEF body `φ` and a PEF head `ψ` over the variables
`x̄`, and reads `∀x̄. (φ → ψ)`. Every PEF is equivalent to a disjunction `⋁ᵢ ∃ȳᵢ. ⋀ⱼ Pᵢⱼ`
(Lemma 4.1.1), and every geometric sequent is equivalent to a set of *standard* sequents whose
body has neither `∃` nor `∨` (Lemma 4.1.2); see §4.1 of Saghafi, *A Framework for Exploring
Finite Models*, and the normal-form proposition of Vickers, [*Geometric Logic in Computer
Science*][glics]. An arbitrary first-order formula is only equisatisfiable to a geometric theory
(Theorem 4.2.2), through Skolemization; this conversion Skolemizes exactly the existential
quantifiers whose scope is not a PEF.

Starting from the sequent `⊤ ⊢ φ` over the free variables of an [`NNF`] `φ`:

1. `⊢ ∀x. φ` adds `x` to the sequent's variables, renamed apart when its name is taken.
2. A conjunction outside every `∃` splits the sequent into one sequent per conjunct. A
   conjunction under an `∃` never splits.
3. A disjunction outside every `∃` distributes over the conjunctions of its sides, and a
   negative literal `¬A` outside every `∃` moves `A` to the body: `φ ⊢ ¬A ∨ ψ` becomes
   `φ ∧ A ⊢ ψ`.
4. `∃ȳ. α` whose scope `α` is a PEF stays in the head as disjuncts `∃ȳ. ⋀ atoms`: `∃`
   distributes over `∨`, nested `∃`s flatten into one disjunct, a conjunction is the cross
   product of the disjuncts of its sides, and an existential equated to another variable is
   substituted away.
5. `∃ȳ. (α ∨ β)` whose scope is not a PEF becomes `∃ȳ. α ∨ ∃ȳ. β`. Any other `∃y. α` whose
   scope is not a PEF replaces `y` by a Skolem term over the sequent's variables in scope, a
   constant when there are none, and continues with `α`. Skolem symbols arise nowhere else.
   Each Skolem term `t` minted over `x̄` also yields the *totality* sequent `⊤ ⊢x̄ ∃y. y = t`:
   a Skolem function is total, but the chase only creates the elements a head asks for, so a
   term that occurs only in bodies would otherwise never denote an element.
6. A body only receives atoms, through rule 3, so it never holds `∃` or `∨`.
7. `⊥` as the head leaves a failure sequent with an empty head. A sequent whose head is `⊤`,
   or has a `⊤` disjunct, is true and is dropped. Equations `t = t` and `⊥` disjuncts are
   dropped.

[glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
[`NNF`]: crate::transform::NNF
*/
use super::{ToNNF, NNF, PCF};
use crate::syntax::{
    formula::{clause::Literal, *},
    term::Complex,
    Const, Error, Func, Sig, Var, FOF,
};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

/// Is a disjunct in the head of a [`Geometric`] sequent: a list of existentially quantified
/// variables over a conjunction of atoms.
///
/// The existentials of a disjunct are pairwise distinct, distinct from the variables of its
/// sequent, and each occurs in the atoms; a disjunct without atoms keeps a single existential,
/// claiming that an element exists.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Disjunct {
    existentials: Vec<Var>,
    atoms: PCF,
}

impl Disjunct {
    /// Returns the existentially quantified variables of `self`.
    #[inline(always)]
    pub fn existentials(&self) -> &[Var] {
        &self.existentials
    }

    /// Returns the conjunction of atoms of `self`.
    #[inline(always)]
    pub fn atoms(&self) -> &PCF {
        &self.atoms
    }

    fn is_top(&self) -> bool {
        self.existentials.is_empty() && self.atoms.is_empty()
    }

    fn and(&self, other: &Self) -> Self {
        Self {
            existentials: [self.existentials.clone(), other.existentials.clone()].concat(),
            atoms: self.atoms.union(&other.atoms),
        }
    }

    fn exists(self, variables: &[Var]) -> Self {
        Self {
            existentials: [variables.to_vec(), self.existentials].concat(),
            atoms: self.atoms,
        }
    }

    // Substitutes away the existentials equated to a variable, then drops reflexive equations
    // and the existentials that no longer occur.
    fn simplify(mut self) -> Self {
        while let Some((gone, kept)) = self.equated() {
            self = self.substitute_existential(&gone, kept);
        }
        let atoms: PCF = self
            .atoms
            .into_iter()
            .filter(|a| !a.is_reflexive())
            .collect();
        let witness = self.existentials.first().cloned();
        let occurring: HashSet<&Var> = atoms.free_vars().into_iter().collect();
        let mut existentials = self.existentials;
        existentials.retain(|v| occurring.contains(v));
        if atoms.is_empty() {
            existentials = witness.into_iter().collect();
        }
        Self {
            existentials,
            atoms,
        }
    }

    // Returns an existential equated to a different variable, paired with that variable.
    fn equated(&self) -> Option<(Var, Var)> {
        self.atoms.iter().find_map(|atomic| {
            let (left, right) = atomic.variable_equation()?;
            if left == right {
                None
            } else if self.existentials.contains(left) {
                Some((left.clone(), right.clone()))
            } else if self.existentials.contains(right) {
                Some((right.clone(), left.clone()))
            } else {
                None
            }
        })
    }

    fn substitute_existential(self, gone: &Var, kept: Var) -> Self {
        let substitution = HashMap::from([(gone.clone(), Complex::from(kept))]);
        Self {
            existentials: self
                .existentials
                .into_iter()
                .filter(|v| v != gone)
                .collect(),
            atoms: self.atoms.substitute(&substitution),
        }
    }
}

impl From<Atomic<Complex>> for Disjunct {
    fn from(value: Atomic<Complex>) -> Self {
        Self {
            existentials: Vec::new(),
            atoms: value.into(),
        }
    }
}

impl Formula for Disjunct {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        self.atoms.signature()
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.atoms
            .free_vars()
            .into_iter()
            .filter(|v| !self.existentials.contains(v))
            .collect()
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            existentials: self.existentials.clone(),
            atoms: self.atoms.transform_term(f),
        }
    }
}

impl std::fmt::Display for Disjunct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self.clone()).fmt(f)
    }
}

impl From<Disjunct> for FOF {
    fn from(value: Disjunct) -> Self {
        let atoms = FOF::from(value.atoms);
        if value.existentials.is_empty() {
            atoms
        } else {
            FOF::exists(value.existentials, atoms)
        }
    }
}

/// Represents a standard geometric sequent (Lemma 4.1.2 of the dissertation): a body that is a
/// conjunction of atoms over the sequent's variables, implying a head that is a disjunction of
/// [`Disjunct`]s. The sequent's variables are universally quantified; an empty head is `⊥`.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Geometric {
    body: PCF,
    head: Vec<Disjunct>,
}

impl Geometric {
    /// Returns the body of `self`.
    #[inline(always)]
    pub fn body(&self) -> &PCF {
        &self.body
    }

    /// Returns the disjuncts in the head of `self`.
    #[inline(always)]
    pub fn head(&self) -> &[Disjunct] {
        &self.head
    }

    // Returns the sequents `⊢ ⋁ disjuncts`: none when a disjunct is `⊤`.
    fn claim(disjuncts: Vec<Disjunct>) -> Vec<Self> {
        if disjuncts.iter().any(Disjunct::is_top) {
            return Vec::new();
        }
        vec![Self {
            body: PCF::default(),
            head: disjuncts.into_iter().unique().collect(),
        }]
    }

    // Returns the sequent `⊤ ⊢ ∃y. y = term` over `universals`, the variables of `term`.
    fn total(term: Complex, universals: &[Var]) -> Self {
        let y = Var::from("y").apart(|v| universals.contains(v));
        let equation = Atomic::from(Equals {
            left: Complex::from(y.clone()),
            right: term,
        });
        Self {
            body: PCF::default(),
            head: vec![Disjunct::from(equation).exists(&[y])],
        }
    }

    // Returns the sequent `atomic ⊢ ⊥`.
    fn deny(atomic: Atomic<Complex>) -> Self {
        Self {
            body: [atomic].into_iter().filter(|a| !a.is_reflexive()).collect(),
            head: Vec::new(),
        }
    }

    // Returns the sequents of the disjunction of two conjunctions of sequents.
    fn or(left: &[Self], right: &[Self]) -> Vec<Self> {
        left.iter()
            .cartesian_product(right)
            .map(|(l, r)| l.merge(r))
            .unique()
            .collect()
    }

    fn merge(&self, other: &Self) -> Self {
        Self {
            body: self.body.union(&other.body),
            head: self
                .head
                .iter()
                .chain(&other.head)
                .unique()
                .cloned()
                .collect(),
        }
    }
}

impl Formula for Geometric {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        let head = self.head.iter().map(Disjunct::signature);
        Sig::from_signatures(
            std::iter::once(self.body.signature())
                .chain(head)
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.body
            .free_vars()
            .into_iter()
            .chain(self.head.iter().flat_map(Disjunct::free_vars))
            .unique()
            .collect()
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            body: self.body.transform_term(f),
            head: self.head.iter().map(|d| d.transform_term(f)).collect(),
        }
    }
}

impl std::fmt::Display for Geometric {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self.clone()).fmt(f)
    }
}

impl From<Geometric> for FOF {
    fn from(value: Geometric) -> Self {
        let head = value
            .head
            .into_iter()
            .map(FOF::from)
            .reduce(|left, right| left.or(right))
            .unwrap_or(FOF::Bottom);
        FOF::from(value.body).implies(head)
    }
}

/// Is the trait of [`Formula`] types that can be transformed to a list of standard
/// [`Geometric`] sequents.
pub trait ToGeometric: Formula {
    /// Is similar to [`ToGeometric::geometric`] but uses custom closures to generate Skolem
    /// function and constant names.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToGeometric;
    ///
    /// let mut c_counter = 0;
    /// let mut f_counter = 0;
    /// let mut const_generator = || {
    ///     let c = c_counter;
    ///     c_counter += 1;
    ///     format!("skolem_const{}", c).into()
    /// };
    /// let mut fn_generator = || {
    ///     let c = f_counter;
    ///     f_counter += 1;
    ///     format!("skolem_fn{}", c).into()
    /// };
    /// let formula: FOF = "∃ y. ∀ z. P(x, y, z)".parse().unwrap();
    /// let sequents = formula.geometric_with(&mut const_generator, &mut fn_generator);
    ///
    /// assert_eq!("⊤ → P(x, skolem_fn0(x), z)", sequents[0].to_string());
    /// ```
    fn geometric_with<CG, FG>(
        &self,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Vec<Geometric>
    where
        CG: FnMut() -> Const,
        FG: FnMut() -> Func;

    /// Transforms `self` to a list of standard geometric sequents whose conjunction is
    /// equisatisfiable to `self`, and equivalent to it when no Skolem symbol is needed. The free
    /// variables of `self` are read as universally quantified, and Skolem symbols are named
    /// `c#N` (constants) and `f#N` (functions).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToGeometric;
    ///
    /// let formula: FOF = "P(x) -> exists y. (Q(x, y) & R(y))".parse().unwrap();
    /// let sequents = formula.geometric();
    ///
    /// assert_eq!("P(x) → (∃ y. (Q(x, y) ∧ R(y)))", sequents[0].to_string());
    /// ```
    fn geometric(&self) -> Vec<Geometric> {
        let mut c_counter = 0;
        let mut f_counter = 0;
        let mut const_generator = || {
            let name = format!("c#{}", c_counter);
            c_counter += 1;
            name.into()
        };
        let mut fn_generator = || {
            let name = format!("f#{}", f_counter);
            f_counter += 1;
            name.into()
        };

        self.geometric_with(&mut const_generator, &mut fn_generator)
    }
}

impl ToGeometric for NNF {
    fn geometric_with<CG, FG>(
        &self,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Vec<Geometric>
    where
        CG: FnMut() -> Const,
        FG: FnMut() -> Func,
    {
        let universals: Vec<Var> = self.free_vars().into_iter().cloned().collect();
        let mut converter = Converter {
            const_generator,
            fn_generator,
            universals: universals.iter().cloned().collect(),
            existentials: HashSet::new(),
            totality: Vec::new(),
        };
        let scope = Scope {
            universals,
            env: HashMap::new(),
        };
        let sequents = converter.sequents(self, &scope);
        sequents
            .into_iter()
            .chain(converter.totality)
            .unique()
            .collect()
    }
}

impl<T: ToNNF> ToGeometric for T {
    fn geometric_with<CG, FG>(
        &self,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Vec<Geometric>
    where
        CG: FnMut() -> Const,
        FG: FnMut() -> Func,
    {
        self.nnf().geometric_with(const_generator, fn_generator)
    }
}

// The bindings in effect at a position of the source formula: the sequent's variables in scope,
// in binding order, and the terms that replace the source's bound variables.
#[derive(Clone)]
struct Scope {
    universals: Vec<Var>,
    env: HashMap<Var, Complex>,
}

impl Scope {
    fn bind(&self, variable: &Var, term: Complex) -> Self {
        let mut env = self.env.clone();
        env.insert(variable.clone(), term);
        Self {
            universals: self.universals.clone(),
            env,
        }
    }

    fn universal(&self, variable: &Var, name: Var) -> Self {
        let mut scope = self.bind(variable, name.clone().into());
        scope.universals.push(name);
        scope
    }

    fn apply(&self, atomic: &Atomic<Complex>) -> Atomic<Complex> {
        atomic.substitute(&self.env)
    }
}

// Converts a formula outside every existential quantifier. Universals are named apart from every
// variable named before them, and existentials from every universal, so sequents and disjuncts
// combine without renaming. The totality sequents of the Skolem terms are kept apart, since they
// hold unconditionally and never join a disjunction.
struct Converter<'g, CG, FG> {
    const_generator: &'g mut CG,
    fn_generator: &'g mut FG,
    universals: HashSet<Var>,
    existentials: HashSet<Var>,
    totality: Vec<Geometric>,
}

impl<CG, FG> Converter<'_, CG, FG>
where
    CG: FnMut() -> Const,
    FG: FnMut() -> Func,
{
    fn sequents(&mut self, formula: &NNF, scope: &Scope) -> Vec<Geometric> {
        match formula {
            NNF::Top => Vec::new(),
            NNF::Bottom => vec![Geometric::default()],
            NNF::Literal(Literal::Pos(atomic)) => {
                Geometric::claim(vec![Disjunct::from(scope.apply(atomic)).simplify()])
            }
            NNF::Literal(Literal::Neg(atomic)) => vec![Geometric::deny(scope.apply(atomic))],
            NNF::And(this) => {
                let mut sequents = self.sequents(&this.left, scope);
                sequents.extend(self.sequents(&this.right, scope));
                sequents
            }
            NNF::Or(this) => {
                let left = self.sequents(&this.left, scope);
                let right = self.sequents(&this.right, scope);
                Geometric::or(&left, &right)
            }
            NNF::Forall(this) => {
                let scope = this
                    .variables
                    .iter()
                    .fold(scope.clone(), |scope, v| self.universal(v, &scope));
                self.sequents(&this.formula, &scope)
            }
            NNF::Exists(this) => self.exists(this.variables.clone(), &this.formula, scope),
        }
    }

    fn exists(&mut self, variables: Vec<Var>, formula: &NNF, scope: &Scope) -> Vec<Geometric> {
        if let NNF::Exists(this) = formula {
            let variables = [variables, this.variables.clone()].concat();
            return self.exists(variables, &this.formula, scope);
        }
        let mut block = Block::new(&self.universals);
        if let Some(disjuncts) = block.exists(&variables, formula, scope) {
            self.existentials.extend(block.names);
            return Geometric::claim(disjuncts);
        }
        match formula {
            NNF::Or(this) => {
                let left = self.exists(variables.clone(), &this.left, scope);
                let right = self.exists(variables, &this.right, scope);
                Geometric::or(&left, &right)
            }
            _ => {
                let scope = self.skolemize(&variables, formula, scope);
                self.sequents(formula, &scope)
            }
        }
    }

    fn universal(&mut self, variable: &Var, scope: &Scope) -> Scope {
        let name = variable.apart(|v| self.universals.contains(v) || self.existentials.contains(v));
        self.universals.insert(name.clone());
        scope.universal(variable, name)
    }

    // Binds the variables of `variables` that `formula` refers to (the last binding of a repeated
    // variable shadows the others) to Skolem terms over the universals in scope.
    fn skolemize(&mut self, variables: &[Var], formula: &NNF, scope: &Scope) -> Scope {
        let free = formula.free_vars();
        variables
            .iter()
            .enumerate()
            .filter(|(i, v)| free.contains(v) && !variables[i + 1..].contains(v))
            .fold(scope.clone(), |scope, (_, v)| {
                let term = self.skolem_term(&scope.universals);
                scope.bind(v, term)
            })
    }

    fn skolem_term(&mut self, universals: &[Var]) -> Complex {
        let term: Complex = if universals.is_empty() {
            (self.const_generator)().into()
        } else {
            (self.fn_generator)().app(universals.iter().map(Complex::from).collect())
        };
        self.totality
            .push(Geometric::total(term.clone(), universals));
        term
    }
}

// Converts the scope of an existential quantifier into disjuncts if it is a positive-existential
// formula, naming its existentials apart from the universals and from each other.
struct Block<'u> {
    universals: &'u HashSet<Var>,
    names: HashSet<Var>,
}

impl<'u> Block<'u> {
    fn new(universals: &'u HashSet<Var>) -> Self {
        Self {
            universals,
            names: HashSet::new(),
        }
    }

    fn exists(&mut self, variables: &[Var], formula: &NNF, scope: &Scope) -> Option<Vec<Disjunct>> {
        let mut scope = scope.clone();
        let mut names = Vec::new();
        for variable in variables {
            let name = variable.apart(|v| self.universals.contains(v) || self.names.contains(v));
            self.names.insert(name.clone());
            scope = scope.bind(variable, name.clone().into());
            names.push(name);
        }
        let disjuncts = self.disjuncts(formula, &scope)?;
        Some(
            disjuncts
                .into_iter()
                .map(|d| d.exists(&names).simplify())
                .collect(),
        )
    }

    fn disjuncts(&mut self, formula: &NNF, scope: &Scope) -> Option<Vec<Disjunct>> {
        match formula {
            NNF::Top => Some(vec![Disjunct::default()]),
            NNF::Bottom => Some(Vec::new()),
            NNF::Literal(Literal::Pos(atomic)) => Some(vec![scope.apply(atomic).into()]),
            NNF::Literal(Literal::Neg(_)) | NNF::Forall(_) => None,
            NNF::And(this) => {
                let left = self.disjuncts(&this.left, scope)?;
                let right = self.disjuncts(&this.right, scope)?;
                Some(
                    left.iter()
                        .cartesian_product(&right)
                        .map(|(l, r)| l.and(r))
                        .collect(),
                )
            }
            NNF::Or(this) => {
                let mut left = self.disjuncts(&this.left, scope)?;
                left.extend(self.disjuncts(&this.right, scope)?);
                Some(left)
            }
            NNF::Exists(this) => self.exists(&this.variables, &this.formula, scope),
        }
    }
}

trait VarEx {
    // Returns `self` with backticks appended until it is not `taken`.
    fn apart(&self, taken: impl Fn(&Var) -> bool) -> Var;
}

impl VarEx for Var {
    fn apart(&self, taken: impl Fn(&Var) -> bool) -> Var {
        let mut name = self.clone();
        while taken(&name) {
            name = format!("{}`", name.name()).into();
        }
        name
    }
}

trait AtomicEx {
    fn is_reflexive(&self) -> bool;

    fn variable_equation(&self) -> Option<(&Var, &Var)>;
}

impl AtomicEx for Atomic<Complex> {
    fn is_reflexive(&self) -> bool {
        matches!(self, Atomic::Equals(this) if this.left == this.right)
    }

    fn variable_equation(&self) -> Option<(&Var, &Var)> {
        match self {
            Atomic::Equals(Equals {
                left: Complex::Var(left),
                right: Complex::Var(right),
            }) => Some((left, right)),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        syntax::{Theory, EQ_SYM},
        transform::{ToGNF, PCF},
    };
    use std::{fs, path::PathBuf};

    // Converts `text` and prints one sequent per line.
    fn geometric(text: &str) -> String {
        let formula: FOF = text.parse().unwrap();
        formula.geometric().iter().join("\n")
    }

    fn existentials(text: &str) -> Vec<Vec<Var>> {
        let formula: FOF = text.parse().unwrap();
        formula
            .geometric()
            .iter()
            .flat_map(|g| g.head().iter().map(|d| d.existentials().to_vec()))
            .collect()
    }

    fn vars(names: &[&str]) -> Vec<Var> {
        names.iter().map(|&n| Var::from(n)).collect()
    }

    // The theories in the fixture directory `dir`, relative to the repository root.
    fn fixtures(dir: &str) -> Vec<(PathBuf, Theory<FOF>)> {
        let mut paths: Vec<PathBuf> = fs::read_dir(format!("../theories/{}", dir))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|e| e == "raz"))
            .collect();
        paths.sort();
        paths
            .into_iter()
            .map(|path| {
                let theory = fs::read_to_string(&path).unwrap().parse().unwrap();
                (path, theory)
            })
            .collect()
    }

    fn all_fixtures() -> Vec<(PathBuf, Theory<FOF>)> {
        [fixtures("core"), fixtures("examples")].concat()
    }

    // The signature of `formulae` without Skolem symbols, as sorted printable entries.
    fn user_signature(formulae: impl IntoIterator<Item = FOF>) -> Vec<String> {
        let theory: Theory<FOF> = formulae.into_iter().collect();
        let sig = theory.signature().unwrap();
        let user = |name: &str| !name.contains('#');
        let constants = sig
            .constants()
            .iter()
            .map(|c| c.to_string())
            .filter(|c| user(c));
        let functions = sig
            .functions()
            .values()
            .filter(|f| user(f.symbol.name()))
            .map(|f| format!("{}/{}", f.symbol, f.arity));
        let predicates = sig
            .predicates()
            .values()
            .filter(|p| p.symbol.name() != EQ_SYM)
            .map(|p| format!("{}/{}", p.symbol, p.arity));
        constants
            .chain(functions)
            .chain(predicates)
            .sorted()
            .collect()
    }

    #[test]
    fn universal_joins_the_variables() {
        assert_eq!("P(x) → Q(x, y)", geometric("forall y. (P(x) -> Q(x, y))"));
    }

    #[test]
    fn universal_renames_apart_from_a_taken_name() {
        assert_eq!(
            "P(x) → Q(x`)",
            geometric("forall x. (P(x) -> forall x. Q(x))")
        );
        assert_eq!(
            "⊤ → (P(x) ∨ Q(x`))",
            geometric("(forall x. P(x)) | (forall x. Q(x))")
        );
    }

    #[test]
    fn conjunction_outside_exists_splits() {
        assert_eq!("P(x) → Q(x)\nP(x) → R(x)", geometric("P(x) -> Q(x) & R(x)"));
    }

    #[test]
    fn conjunction_under_exists_does_not_split() {
        assert_eq!(
            "P(x) → (∃ y. (Q(x, y) ∧ R(y)))",
            geometric("P(x) -> exists y. (Q(x, y) & R(y))")
        );
        assert_eq!(
            vec![vars(&["y"])],
            existentials("P(x) -> exists y. (Q(x, y) & R(y))")
        );
    }

    #[test]
    fn negative_literal_moves_to_body() {
        assert_eq!("(P(x) ∧ Q(x)) → R(x)", geometric("~P(x) | ~Q(x) | R(x)"));
        assert_eq!("P(x) → ⟘", geometric("P(x) -> false"));
    }

    #[test]
    fn disjunction_distributes_over_conjunction() {
        assert_eq!(
            "P(x) → (R(x) ∨ S(x))\nQ(x) → (R(x) ∨ S(x))",
            geometric("(~P(x) & ~Q(x)) | R(x) | S(x)")
        );
    }

    #[test]
    fn body_disjunction_splits() {
        assert_eq!(
            "(P(x) ∧ Q(x)) → S(x)\nR(x) → S(x)",
            geometric("(P(x) & Q(x)) | R(x) -> S(x)")
        );
    }

    #[test]
    fn body_exists_becomes_universal() {
        assert_eq!("P(x, y) → Q(x)", geometric("(exists y. P(x, y)) -> Q(x)"));
    }

    #[test]
    fn exists_and_atom_are_two_disjuncts() {
        assert_eq!(
            "P(x) → ((∃ y. Q(x, y)) ∨ R(x))",
            geometric("P(x) -> (exists y. Q(x, y)) | R(x)")
        );
        assert_eq!(
            vec![vars(&["y"]), vec![]],
            existentials("P(x) -> (exists y. Q(x, y)) | R(x)")
        );
    }

    #[test]
    fn exists_distributes_over_disjunction() {
        assert_eq!(
            "⊤ → ((∃ y. Q(y)) ∨ (∃ y. R(y)))",
            geometric("exists y. (Q(y) | R(y))")
        );
    }

    #[test]
    fn nested_exists_flatten_into_one_disjunct() {
        assert_eq!(
            "⊤ → (∃ y, z. (Q(x, y) ∧ S(y, z)))",
            geometric("exists y. (Q(x, y) & exists z. S(y, z))")
        );
        assert_eq!(
            vec![vars(&["y", "z"])],
            existentials("exists y. (Q(x, y) & exists z. S(y, z))")
        );
    }

    #[test]
    fn exists_conjunction_is_a_cross_product() {
        assert_eq!(
            "⊤ → ((∃ y. (P(y) ∧ R(y))) ∨ (∃ y. (Q(y) ∧ R(y))))",
            geometric("exists y. ((P(y) | Q(y)) & R(y))")
        );
    }

    #[test]
    fn nested_exists_with_a_taken_name_renames_apart() {
        assert_eq!("P(x) → (∃ x`. Q(x`))", geometric("P(x) -> exists x. Q(x)"));
        assert_eq!(
            "⊤ → (∃ y, y`. (P(y) ∧ Q(y`)))",
            geometric("exists y. (P(y) & exists y. Q(y))")
        );
    }

    #[test]
    fn existential_equated_to_a_universal_is_substituted() {
        assert_eq!(
            "P(x) → Q(x)",
            geometric("forall x. (P(x) -> exists y. (y = x & Q(y)))")
        );
    }

    #[test]
    fn existential_equated_to_an_existential_is_substituted() {
        assert_eq!("⊤ → (∃ z. P(z))", geometric("exists y, z. (P(y) & y = z)"));
    }

    #[test]
    fn existential_equated_to_a_function_term_stays() {
        assert_eq!(
            "P(x) → (∃ y. (Q(y) ∧ y = f(x)))",
            geometric("P(x) -> exists y. (y = f(x) & Q(y))")
        );
    }

    #[test]
    fn exists_without_atoms_claims_an_element() {
        assert_eq!("⊤ → (∃ y. ⊤)", geometric("true -> exists y. y = y"));
        assert_eq!(vec![vars(&["y"])], existentials("true -> exists y. y = y"));
    }

    #[test]
    fn exists_over_universal_is_skolemized_to_a_constant() {
        assert_eq!(
            "⊤ → Q(u, 'c#0)\n⊤ → (∃ y. y = 'c#0)",
            geometric("exists y. forall u. Q(u, y)")
        );
    }

    #[test]
    fn exists_over_negative_literal_is_skolemized_over_universals() {
        assert_eq!(
            "⊤ → P(x, f#0(x))\nQ(f#0(x)) → R(f#0(x))\n⊤ → (∃ y. y = f#0(x))",
            geometric("forall x. exists y. (P(x, y) & (Q(y) -> R(y)))")
        );
    }

    #[test]
    fn a_skolem_term_only_in_a_body_is_total() {
        assert_eq!(
            "P('c#0) → (∃ z. Q(z))\n⊤ → (∃ y. y = 'c#0)",
            geometric("exists z. (P(z) -> Q(z))")
        );
    }

    #[test]
    fn totality_names_its_existential_apart_from_the_universals() {
        assert_eq!(
            "Q(y, f#0(y)) → ⟘\n⊤ → (∃ y`. y` = f#0(y))",
            geometric("forall y. exists z. ~Q(y, z)")
        );
    }

    #[test]
    fn totality_never_joins_a_disjunction() {
        assert_eq!(
            "⊤ → (P('a) ∨ Q('c#0, u))\n⊤ → (∃ y. y = 'c#0)",
            geometric("P('a) | exists z. forall u. Q(z, u)")
        );
    }

    #[test]
    fn exists_skolemizes_only_the_non_positive_disjunct() {
        assert_eq!(
            "⊤ → ((∃ y. P(y)) ∨ Q(u, 'c#0))\n⊤ → (∃ y. y = 'c#0)",
            geometric("exists y. (P(y) | forall u. Q(u, y))")
        );
    }

    #[test]
    fn bottom_head_is_a_failure_sequent() {
        assert_eq!("⊤ → ⟘", geometric("false"));
        assert_eq!("⊤ → ⟘", geometric("~(x = x)"));
        assert_eq!("P(x) → ⟘", geometric("P(x) -> exists y. false"));
    }

    #[test]
    fn true_head_drops_the_sequent() {
        assert_eq!("", geometric("P(x) -> true"));
        assert_eq!("", geometric("x = x"));
        assert_eq!("", geometric("P(x) -> Q(x) | exists y. y = x"));
    }

    #[test]
    fn bottom_disjunct_and_reflexive_equation_are_dropped() {
        assert_eq!("P(x) → Q(x)", geometric("P(x) -> Q(x) | false"));
        assert_eq!(
            "(P(x) ∧ x = y) → Q(x)",
            geometric("P(x) & x = x & x = y -> Q(x)")
        );
    }

    #[test]
    fn free_vars_exclude_existentials() {
        let formula: FOF = "P(x) -> exists y. Q(x, y, z)".parse().unwrap();
        let sequent = &formula.geometric()[0];
        assert_eq!(
            vars(&["x", "z"]),
            sequent.free_vars().into_iter().cloned().collect_vec()
        );
    }

    #[test]
    fn geometric_with_names_skolem_symbols() {
        let formula: FOF = "forall x. exists y. ~P(x, y)".parse().unwrap();
        let sequents = formula.geometric_with(&mut || "c".into(), &mut || "sk".into());
        assert_eq!(
            "P(x, sk(x)) → ⟘\n⊤ → (∃ y. y = sk(x))",
            sequents.iter().join("\n")
        );
    }

    #[test]
    fn transform_term_rewrites_body_and_head() {
        let formula: FOF = "P(x) -> exists y. Q(x, y)".parse().unwrap();
        let constant = |t: &Complex| match t {
            Complex::Var(v) if v.name() == "x" => Complex::from(Const::from("a")),
            _ => t.clone(),
        };
        let sequent = formula.geometric()[0].transform_term(&constant);
        assert_eq!("P('a) → (∃ y. Q('a, y))", sequent.to_string());
        assert_eq!(&PCF::from(fof_atom("P('a)")), sequent.body());
    }

    fn fof_atom(text: &str) -> Atomic<Complex> {
        match text.parse::<FOF>().unwrap() {
            FOF::Atom(atom) => atom.into(),
            _ => unreachable!("not an atom"),
        }
    }

    #[test]
    fn fixtures_keep_the_signature() {
        for (path, theory) in all_fixtures() {
            let mut sequents = 0;
            let mut gnfs = 0;
            for formula in theory.iter() {
                let new = formula.geometric();
                let old = formula.gnf();
                assert_eq!(
                    user_signature(old.iter().map(FOF::from)),
                    user_signature(new.iter().cloned().map(FOF::from)),
                    "{} in {:?}",
                    formula,
                    path
                );
                sequents += new.len();
                gnfs += old.len();
            }
            println!("{:?}: geometric {} gnf {}", path, sequents, gnfs);
        }
    }

    #[test]
    fn standard_sequents_round_trip() {
        let mut checked = 0;
        for (_, theory) in all_fixtures() {
            let sequents: Theory<Geometric> = theory.iter().flat_map(|f| f.geometric()).collect();
            let printed = sequents.to_string();
            if printed.contains('#') || printed.contains('`') {
                continue;
            }
            let reparsed: Theory<FOF> = sequents
                .iter()
                .cloned()
                .map(FOF::from)
                .collect::<Theory<FOF>>()
                .iter()
                .map(|f| format!("{};", f))
                .join("\n")
                .parse()
                .unwrap();
            let again: Theory<Geometric> = reparsed.iter().flat_map(|f| f.geometric()).collect();
            assert_eq!(printed, again.to_string());
            checked += 1;
        }
        assert!(checked > 0);
    }
}
