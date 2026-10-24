/*! Defines formulae in Geometric Normal Form (GNF), standard geometric sequents, and implements
a conversion from first-order formulae to [`GNF`] sequents that Skolemizes an existential
quantifier only when it must.

A *positive-existential formula* (PEF) is built from atoms, equations, `⊤`, `⊥`, `∧`, `∨` and
`∃`. A *geometric sequent* `φ ⊢x̄ ψ` has a PEF body `φ` and a PEF head `ψ` over the variables
`x̄`, and reads `∀x̄. (φ → ψ)`. Every PEF is equivalent to a disjunction `⋁ᵢ ∃ȳᵢ. ⋀ⱼ Pᵢⱼ`
(Lemma 4.1.1), and every geometric sequent is equivalent to a set of *standard* sequents whose
body has neither `∃` nor `∨` (Lemma 4.1.2); see §4.1 of Saghafi, *A Framework for Exploring
Finite Models*, and the normal-form proposition of Vickers, [*GNF Logic in Computer
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
   A Skolem term `t` minted over `x̄` that is a constant, or occurs in a body of the sequents
   of `α`, also yields the *totality* claim `⊢x̄ ∃y. y = t`, conjoined to the conversion of
   `α` so that the negative literals of the enclosing disjunctions become its body. A Skolem
   function is total, but the chase only creates the elements a head asks for, so a term in a
   body alone would never denote an element, and a constant in a head alone would leave the
   domain empty when no body holds. A term that occurs only in heads needs no claim: the chase
   creates it wherever a head that mentions it must hold, and anywhere else any element
   witnesses `∃y. α`. Claiming no more than that keeps the chase from building every term of
   a function over the whole domain.
6. A body only receives atoms, through rule 3, so it never holds `∃` or `∨`.
7. `⊥` as the head leaves a failure sequent with an empty head. A sequent whose head is `⊤`,
   or has a `⊤` disjunct (one whose atoms are all equations `x = x`), is true and is dropped.
   `⊥` disjuncts and equations `y = y` over an existential are dropped. Any other equation
   `t = t` stays: over a variable `x` of the sequent it keeps `x` among the sequent's
   variables, so the sequent still ranges over the domain (and holds vacuously when it is
   empty); over a constant or a function application it claims that `t` denotes an element,
   since functions are partial in the chase.

[glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
[`NNF`]: crate::transform::NNF
*/
use super::{ToNNF, NNF};
use crate::syntax::{
    formula::{literal::Literal, *},
    term::Complex,
    Const, Error, Func, Sig, Var, FOF,
};
use itertools::Itertools;
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap, HashSet},
    iter::FromIterator,
    ops::Deref,
};

// A positive literal is simply an atomic formula.
type PosLiteral = Atomic<Complex>;

/// A Positive Conjunctive Formula (PCF) represents a collection of [`Atomic`]s, interpreted
/// as a conjunction of positive literals: the body of a [`GNF`] and the atoms of a [`Disjunct`].
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct PCF(BTreeSet<PosLiteral>);

impl PCF {
    /// Consumes `self` and returns its underlying list of positive literals.
    pub fn into_literals(self) -> BTreeSet<PosLiteral> {
        self.0
    }

    /// Returns a new clause, resulting from joining the positive literals of `self`
    /// and `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().collect()
    }
}

impl Deref for PCF {
    type Target = BTreeSet<PosLiteral>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<PosLiteral> for PCF {
    fn from(value: PosLiteral) -> Self {
        vec![value].into_iter().collect()
    }
}

impl From<Atom<Complex>> for PCF {
    fn from(value: Atom<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().collect()
    }
}

impl From<Equals<Complex>> for PCF {
    fn from(value: Equals<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().collect()
    }
}

impl FromIterator<PosLiteral> for PCF {
    fn from_iter<T: IntoIterator<Item = PosLiteral>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for PCF {
    type Item = PosLiteral;

    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl From<Vec<PosLiteral>> for PCF {
    fn from(value: Vec<PosLiteral>) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Formula for PCF {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.iter()
            .flat_map(|lit| lit.free_vars())
            .unique()
            .collect()
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        self.iter().map(|lit| lit.transform_term(f)).collect()
    }
}

impl From<PCF> for FOF {
    fn from(value: PCF) -> Self {
        value
            .into_literals()
            .into_iter()
            .sorted()
            .map(|atomic| match atomic {
                Atomic::Atom(this) => FOF::from(this),
                Atomic::Equals(this) => this.into(),
            })
            .reduce(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

impl From<&PCF> for FOF {
    fn from(value: &PCF) -> Self {
        value.clone().into()
    }
}

/// Is a disjunct in the head of a [`GNF`] sequent: a list of existentially quantified
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

    // Is `self` true under every assignment of the sequent's variables?
    fn is_top(&self) -> bool {
        self.existentials.is_empty() && self.atoms.iter().all(AtomicEx::is_reflexive)
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

    // Substitutes away the existentials equated to a variable, then drops the equations `v = v`
    // that `self` does not need and the existentials that no longer occur.
    fn simplify(mut self) -> Self {
        while let Some((gone, kept)) = self.equated() {
            self = self.substitute_existential(&gone, kept);
        }
        let atoms: PCF = self
            .atoms
            .iter()
            .filter(|a| !self.redundant(a))
            .cloned()
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

    // Is `atomic` an equation `v = v` that adds nothing: `v` is an existential, or occurs in
    // another atom? An equation `x = x` alone keeps the sequent's variable `x`.
    fn redundant(&self, atomic: &Atomic<Complex>) -> bool {
        match atomic.variable_equation() {
            Some((v, w)) if v == w => {
                self.existentials.contains(v)
                    || self
                        .atoms
                        .iter()
                        .any(|other| other != atomic && other.free_vars().contains(&v))
            }
            _ => false,
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
pub struct GNF {
    body: PCF,
    head: Vec<Disjunct>,
}

impl GNF {
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

    /// Returns the disjuncts of the head of `self`, each with the variables of `self` that its
    /// existentials depend on, in the order of [`Formula::free_vars`]: those of the body, so
    /// that every trigger of the sequent has its own witnesses, and those of the disjunct. A
    /// variable that only other disjuncts mention is left out: its quantifier can be pushed
    /// into them, so it never scopes over the existentials, and a witness over it would name a
    /// new element for every element of the domain.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToGNF;
    ///
    /// let formula: FOF = "P(x) -> Q(u) | exists z. R(x, z)".parse().unwrap();
    /// let sequent = &formula.gnf()[0];
    /// let scopes: Vec<String> = sequent
    ///     .scopes()
    ///     .map(|(_, vars)| vars.iter().map(|v| v.to_string()).collect())
    ///     .collect();
    /// assert_eq!(vec!["xu".to_string(), "x".to_string()], scopes);
    /// ```
    pub fn scopes(&self) -> impl Iterator<Item = (&Disjunct, Vec<&Var>)> {
        let universals = self.free_vars();
        let body = self.body.free_vars();
        self.head.iter().map(move |disjunct| {
            let seen = disjunct.free_vars();
            let scope = universals
                .iter()
                .filter(|v| body.contains(v) || seen.contains(v))
                .copied()
                .collect();
            (disjunct, scope)
        })
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

    // Returns the claim `⊢ ∃y. y = term` over `universals`, the variables of `term`.
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

    // Does `term` occur in a body of `sequents`?
    fn mention(sequents: &[Self], term: &Complex) -> bool {
        sequents
            .iter()
            .any(|s| s.body.iter().any(|atomic| atomic.mentions(term)))
    }

    // Returns the sequent `atomic ⊢ ⊥`.
    fn deny(atomic: Atomic<Complex>) -> Self {
        Self {
            body: atomic.into(),
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

impl Formula for GNF {
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

impl std::fmt::Display for GNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self.clone()).fmt(f)
    }
}

impl From<&[Disjunct]> for FOF {
    /// The disjunction of `value`, `⊥` when it is empty: the head of a [`GNF`] sequent.
    fn from(value: &[Disjunct]) -> Self {
        value
            .iter()
            .cloned()
            .map(FOF::from)
            .reduce(|left, right| left.or(right))
            .unwrap_or(FOF::Bottom)
    }
}

impl From<GNF> for FOF {
    fn from(value: GNF) -> Self {
        let head = FOF::from(value.head.as_slice());
        FOF::from(value.body).implies(head)
    }
}

/// Is the trait of [`Formula`] types that can be transformed to a list of standard
/// [`GNF`] sequents.
pub trait ToGNF: Formula {
    /// Is similar to [`ToGNF::gnf`] but uses custom closures to generate Skolem
    /// function and constant names.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToGNF;
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
    /// let sequents = formula.gnf_with(&mut const_generator, &mut fn_generator);
    ///
    /// assert_eq!("⊤ → P(x, skolem_fn0(x), z)", sequents[0].to_string());
    /// ```
    fn gnf_with<CG, FG>(&self, const_generator: &mut CG, fn_generator: &mut FG) -> Vec<GNF>
    where
        CG: FnMut() -> Const,
        FG: FnMut() -> Func;

    /// Transforms `self` to a list of standard geometric sequents whose conjunction is
    /// equisatisfiable to `self`, and equivalent to it when no Skolem symbol is needed. The free
    /// variables of `self` are read as universally quantified, and Skolem symbols are named by
    /// a fresh [`Skolemizer`].
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToGNF;
    ///
    /// let formula: FOF = "P(x) -> exists y. (Q(x, y) & R(y))".parse().unwrap();
    /// let sequents = formula.gnf();
    ///
    /// assert_eq!("P(x) → (∃ y. (Q(x, y) ∧ R(y)))", sequents[0].to_string());
    /// ```
    fn gnf(&self) -> Vec<GNF> {
        Skolemizer::default().gnf(self)
    }
}

/// Mints the Skolem symbols of a theory: constants `c#N` and functions `f#N`, numbered in the
/// order they are minted. `#` is not an identifier character, so a minted symbol never collides
/// with a parsed one. One `Skolemizer` shared by every formula of a theory, and by whatever names
/// elements after the conversion, keeps all their symbols apart.
#[derive(Clone, Debug, Default)]
pub struct Skolemizer {
    constants: usize,
    functions: usize,
}

impl Skolemizer {
    /// A fresh Skolem constant.
    pub fn constant(&mut self) -> Const {
        self.constants += 1;
        format!("c#{}", self.constants - 1).into()
    }

    /// A fresh Skolem function.
    pub fn function(&mut self) -> Func {
        self.functions += 1;
        format!("f#{}", self.functions - 1).into()
    }

    /// A fresh Skolem term over `universals`: a function applied to them, or a constant when
    /// there are none.
    pub fn term(&mut self, universals: &[Var]) -> Complex {
        if universals.is_empty() {
            self.constant().into()
        } else {
            self.function()
                .app(universals.iter().map(Complex::from).collect())
        }
    }

    /// Converts `formula` with [`ToGNF::gnf_with`], naming its Skolem symbols.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::Skolemizer;
    ///
    /// let mut skolemizer = Skolemizer::default();
    /// let first: FOF = "exists x. forall y. P(x, y)".parse().unwrap();
    /// let second: FOF = "exists x. forall y. Q(x, y)".parse().unwrap();
    /// assert_eq!("⊤ → P('c#0, y)", skolemizer.gnf(&first)[0].to_string());
    /// assert_eq!("⊤ → Q('c#1, y)", skolemizer.gnf(&second)[0].to_string());
    /// ```
    pub fn gnf<F: ToGNF + ?Sized>(&mut self, formula: &F) -> Vec<GNF> {
        let skolemizer = RefCell::new(self);
        formula.gnf_with(&mut || skolemizer.borrow_mut().constant(), &mut || {
            skolemizer.borrow_mut().function()
        })
    }
}

impl ToGNF for NNF {
    fn gnf_with<CG, FG>(&self, const_generator: &mut CG, fn_generator: &mut FG) -> Vec<GNF>
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
        };
        let scope = Scope {
            universals,
            env: HashMap::new(),
        };
        converter
            .sequents(self, &scope)
            .into_iter()
            .unique()
            .collect()
    }
}

impl<T: ToNNF> ToGNF for T {
    fn gnf_with<CG, FG>(&self, const_generator: &mut CG, fn_generator: &mut FG) -> Vec<GNF>
    where
        CG: FnMut() -> Const,
        FG: FnMut() -> Func,
    {
        self.nnf().gnf_with(const_generator, fn_generator)
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
// combine without renaming.
struct Converter<'g, CG, FG> {
    const_generator: &'g mut CG,
    fn_generator: &'g mut FG,
    universals: HashSet<Var>,
    existentials: HashSet<Var>,
}

impl<CG, FG> Converter<'_, CG, FG>
where
    CG: FnMut() -> Const,
    FG: FnMut() -> Func,
{
    fn sequents(&mut self, formula: &NNF, scope: &Scope) -> Vec<GNF> {
        match formula {
            NNF::Top => Vec::new(),
            NNF::Bottom => vec![GNF::default()],
            NNF::Literal(Literal::Pos(atomic)) => {
                GNF::claim(vec![Disjunct::from(scope.apply(atomic)).simplify()])
            }
            NNF::Literal(Literal::Neg(atomic)) => vec![GNF::deny(scope.apply(atomic))],
            NNF::And(this) => {
                let mut sequents = self.sequents(&this.left, scope);
                sequents.extend(self.sequents(&this.right, scope));
                sequents
            }
            NNF::Or(this) => {
                let left = self.sequents(&this.left, scope);
                let right = self.sequents(&this.right, scope);
                GNF::or(&left, &right)
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

    fn exists(&mut self, variables: Vec<Var>, formula: &NNF, scope: &Scope) -> Vec<GNF> {
        if let NNF::Exists(this) = formula {
            let variables = [variables, this.variables.clone()].concat();
            return self.exists(variables, &this.formula, scope);
        }
        let mut block = Block::new(&self.universals);
        if let Some(disjuncts) = block.exists(&variables, formula, scope) {
            self.existentials.extend(block.names);
            return GNF::claim(disjuncts);
        }
        match formula {
            NNF::Or(this) => {
                let left = self.exists(variables.clone(), &this.left, scope);
                let right = self.exists(variables, &this.right, scope);
                GNF::or(&left, &right)
            }
            _ => {
                let (scope, terms) = self.skolemize(&variables, formula, scope);
                let mut sequents = self.sequents(formula, &scope);
                let claims: Vec<GNF> = terms
                    .into_iter()
                    .filter(|t| matches!(t, Complex::Const(_)) || GNF::mention(&sequents, t))
                    .map(|t| GNF::total(t, &scope.universals))
                    .collect();
                sequents.extend(claims);
                sequents
            }
        }
    }

    fn universal(&mut self, variable: &Var, scope: &Scope) -> Scope {
        let name = variable.apart(|v| self.universals.contains(v) || self.existentials.contains(v));
        self.universals.insert(name.clone());
        scope.universal(variable, name)
    }

    // Binds the variables of `variables` that `formula` refers to (the last binding of a repeated
    // variable shadows the others) to Skolem terms over the universals in scope, and returns the
    // terms.
    fn skolemize(
        &mut self,
        variables: &[Var],
        formula: &NNF,
        scope: &Scope,
    ) -> (Scope, Vec<Complex>) {
        let free = formula.free_vars();
        let mut scope = scope.clone();
        let mut terms = Vec::new();
        for (i, v) in variables.iter().enumerate() {
            if free.contains(&v) && !variables[i + 1..].contains(v) {
                let term = self.skolem_term(&scope.universals);
                terms.push(term.clone());
                scope = scope.bind(v, term);
            }
        }
        (scope, terms)
    }

    fn skolem_term(&mut self, universals: &[Var]) -> Complex {
        if universals.is_empty() {
            (self.const_generator)().into()
        } else {
            (self.fn_generator)().app(universals.iter().map(Complex::from).collect())
        }
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

trait ComplexEx {
    fn contains(&self, term: &Complex) -> bool;
}

impl ComplexEx for Complex {
    fn contains(&self, term: &Complex) -> bool {
        self == term
            || matches!(self, Complex::App { terms, .. } if terms.iter().any(|t| t.contains(term)))
    }
}

trait AtomicEx {
    fn is_reflexive(&self) -> bool;

    fn mentions(&self, term: &Complex) -> bool;

    fn variable_equation(&self) -> Option<(&Var, &Var)>;
}

impl AtomicEx for Atomic<Complex> {
    fn is_reflexive(&self) -> bool {
        matches!(self.variable_equation(), Some((left, right)) if left == right)
    }

    fn mentions(&self, term: &Complex) -> bool {
        match self {
            Atomic::Atom(this) => this.terms.iter().any(|t| t.contains(term)),
            Atomic::Equals(this) => this.left.contains(term) || this.right.contains(term),
        }
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
        assert_eq_sorted_vecs,
        syntax::{
            signature::{FuncSig, PredSig},
            Theory, EQ_SYM,
        },
        term, v,
    };
    use std::{fs, path::PathBuf};

    // Converts `text` and prints one sequent per line.
    fn gnf(text: &str) -> String {
        let formula: FOF = text.parse().unwrap();
        formula.gnf().iter().join("\n")
    }

    fn existentials(text: &str) -> Vec<Vec<Var>> {
        let formula: FOF = text.parse().unwrap();
        formula
            .gnf()
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

    #[test]
    fn universal_joins_the_variables() {
        assert_eq!("P(x) → Q(x, y)", gnf("forall y. (P(x) -> Q(x, y))"));
    }

    #[test]
    fn universal_renames_apart_from_a_taken_name() {
        assert_eq!("P(x) → Q(x`)", gnf("forall x. (P(x) -> forall x. Q(x))"));
        assert_eq!(
            "⊤ → (P(x) ∨ Q(x`))",
            gnf("(forall x. P(x)) | (forall x. Q(x))")
        );
    }

    #[test]
    fn conjunction_outside_exists_splits() {
        assert_eq!("P(x) → Q(x)\nP(x) → R(x)", gnf("P(x) -> Q(x) & R(x)"));
    }

    #[test]
    fn conjunction_under_exists_does_not_split() {
        assert_eq!(
            "P(x) → (∃ y. (Q(x, y) ∧ R(y)))",
            gnf("P(x) -> exists y. (Q(x, y) & R(y))")
        );
        assert_eq!(
            vec![vars(&["y"])],
            existentials("P(x) -> exists y. (Q(x, y) & R(y))")
        );
    }

    #[test]
    fn negative_literal_moves_to_body() {
        assert_eq!("(P(x) ∧ Q(x)) → R(x)", gnf("~P(x) | ~Q(x) | R(x)"));
        assert_eq!("P(x) → ⟘", gnf("P(x) -> false"));
    }

    #[test]
    fn disjunction_distributes_over_conjunction() {
        assert_eq!(
            "P(x) → (R(x) ∨ S(x))\nQ(x) → (R(x) ∨ S(x))",
            gnf("(~P(x) & ~Q(x)) | R(x) | S(x)")
        );
    }

    #[test]
    fn body_disjunction_splits() {
        assert_eq!(
            "(P(x) ∧ Q(x)) → S(x)\nR(x) → S(x)",
            gnf("(P(x) & Q(x)) | R(x) -> S(x)")
        );
    }

    #[test]
    fn body_exists_becomes_universal() {
        assert_eq!("P(x, y) → Q(x)", gnf("(exists y. P(x, y)) -> Q(x)"));
    }

    #[test]
    fn exists_and_atom_are_two_disjuncts() {
        assert_eq!(
            "P(x) → ((∃ y. Q(x, y)) ∨ R(x))",
            gnf("P(x) -> (exists y. Q(x, y)) | R(x)")
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
            gnf("exists y. (Q(y) | R(y))")
        );
    }

    #[test]
    fn nested_exists_flatten_into_one_disjunct() {
        assert_eq!(
            "⊤ → (∃ y, z. (Q(x, y) ∧ S(y, z)))",
            gnf("exists y. (Q(x, y) & exists z. S(y, z))")
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
            gnf("exists y. ((P(y) | Q(y)) & R(y))")
        );
    }

    #[test]
    fn nested_exists_with_a_taken_name_renames_apart() {
        assert_eq!("P(x) → (∃ x`. Q(x`))", gnf("P(x) -> exists x. Q(x)"));
        assert_eq!(
            "⊤ → (∃ y, y`. (P(y) ∧ Q(y`)))",
            gnf("exists y. (P(y) & exists y. Q(y))")
        );
    }

    #[test]
    fn existential_equated_to_a_universal_is_substituted() {
        assert_eq!(
            "P(x) → Q(x)",
            gnf("forall x. (P(x) -> exists y. (y = x & Q(y)))")
        );
    }

    #[test]
    fn existential_equated_to_an_existential_is_substituted() {
        assert_eq!("⊤ → (∃ z. P(z))", gnf("exists y, z. (P(y) & y = z)"));
    }

    #[test]
    fn existential_equated_to_a_function_term_stays() {
        assert_eq!(
            "P(x) → (∃ y. (Q(y) ∧ y = f(x)))",
            gnf("P(x) -> exists y. (y = f(x) & Q(y))")
        );
    }

    #[test]
    fn exists_without_atoms_claims_an_element() {
        assert_eq!("⊤ → (∃ y. ⊤)", gnf("true -> exists y. y = y"));
        assert_eq!(vec![vars(&["y"])], existentials("true -> exists y. y = y"));
    }

    #[test]
    fn exists_over_universal_is_skolemized_to_a_constant() {
        assert_eq!(
            "⊤ → Q(u, 'c#0)\n⊤ → (∃ y. y = 'c#0)",
            gnf("exists y. forall u. Q(u, y)")
        );
    }

    #[test]
    fn exists_over_negative_literal_is_skolemized_over_universals() {
        assert_eq!(
            "⊤ → P(x, f#0(x))\nQ(f#0(x)) → R(f#0(x))\n⊤ → (∃ y. y = f#0(x))",
            gnf("forall x. exists y. (P(x, y) & (Q(y) -> R(y)))")
        );
    }

    #[test]
    fn a_skolem_term_only_in_a_body_is_total() {
        assert_eq!(
            "P('c#0) → (∃ z. Q(z))\n⊤ → ((∃ y. y = 'c#0) ∨ (∃ z. Q(z)))",
            gnf("exists z. (P(z) -> Q(z))")
        );
    }

    #[test]
    fn totality_names_its_existential_apart_from_the_universals() {
        assert_eq!(
            "Q(y, f#0(y)) → ⟘\n⊤ → (∃ y`. y` = f#0(y))",
            gnf("forall y. exists z. ~Q(y, z)")
        );
    }

    #[test]
    fn totality_is_claimed_where_the_existential_must_hold() {
        assert_eq!(
            "⊤ → (P('a) ∨ Q('c#0, u))\n⊤ → (P('a) ∨ (∃ y. y = 'c#0))",
            gnf("P('a) | exists z. forall u. Q(z, u)")
        );
        assert_eq!(
            "(P(x) ∧ Q(x, f#0(x))) → ⟘\nP(x) → (∃ y. y = f#0(x))",
            gnf("forall x. (P(x) -> exists z. ~Q(x, z))")
        );
    }

    #[test]
    fn a_skolem_function_only_in_heads_is_not_claimed() {
        assert_eq!(
            "P(x) → Q(f#0(x))\nR(x) → S(f#0(x))",
            gnf("forall x. exists y. ((P(x) -> Q(y)) & (R(x) -> S(y)))")
        );
    }

    #[test]
    fn exists_skolemizes_only_the_non_positive_disjunct() {
        assert_eq!(
            "⊤ → ((∃ y. P(y)) ∨ Q(u, 'c#0))\n⊤ → ((∃ y. P(y)) ∨ (∃ y. y = 'c#0))",
            gnf("exists y. (P(y) | forall u. Q(u, y))")
        );
    }

    #[test]
    fn bottom_head_is_a_failure_sequent() {
        assert_eq!("⊤ → ⟘", gnf("false"));
        assert_eq!("x = x → ⟘", gnf("~(x = x)"));
        assert_eq!("P(x) → ⟘", gnf("P(x) -> exists y. false"));
    }

    #[test]
    fn true_head_drops_the_sequent() {
        assert_eq!("", gnf("P(x) -> true"));
        assert_eq!("", gnf("x = x"));
        assert_eq!("", gnf("P(x) -> Q(x) | exists y. y = x"));
    }

    #[test]
    fn bottom_disjunct_and_existential_reflexive_equation_are_dropped() {
        assert_eq!("P(x) → Q(x)", gnf("P(x) -> Q(x) | false"));
        assert_eq!(
            "P(x) → (∃ y. Q(y))",
            gnf("P(x) -> exists y. (y = y & Q(y))")
        );
    }

    #[test]
    fn reflexive_equation_over_a_universal_keeps_its_variable() {
        assert_eq!("y = y → P('a)", gnf("forall y. (y = y -> P('a))"));
        assert_eq!(
            "⊤ → (P('a) ∧ x = x)",
            gnf("exists y. (y = y & x = x & P('a))")
        );
        assert_eq!("⊤ → P(x)", gnf("exists y. (y = x & P(y))"));
    }

    #[test]
    fn reflexive_equation_over_a_term_claims_it_exists() {
        assert_eq!("'b = 'b → P('a)", gnf("'b = 'b -> P('a)"));
        assert_eq!("⊤ → ('a = 'a ∨ P('b))", gnf("'a = 'a | P('b)"));
        assert_eq!("⊤ → f(x) = f(x)", gnf("f(x) = f(x)"));
    }

    #[test]
    fn free_vars_exclude_existentials() {
        let formula: FOF = "P(x) -> exists y. Q(x, y, z)".parse().unwrap();
        let sequent = &formula.gnf()[0];
        assert_eq!(
            vars(&["x", "z"]),
            sequent.free_vars().into_iter().cloned().collect_vec()
        );
    }

    #[test]
    fn gnf_with_names_skolem_symbols() {
        let formula: FOF = "forall x. exists y. ~P(x, y)".parse().unwrap();
        let sequents = formula.gnf_with(&mut || "c".into(), &mut || "sk".into());
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
        let sequent = formula.gnf()[0].transform_term(&constant);
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
    fn standard_sequents_round_trip() {
        let mut checked = 0;
        for (_, theory) in all_fixtures() {
            let sequents: Theory<GNF> = theory.iter().flat_map(|f| f.gnf()).collect();
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
            let again: Theory<GNF> = reparsed.iter().flat_map(|f| f.gnf()).collect();
            assert_eq!(printed, again.to_string());
            checked += 1;
        }
        assert!(checked > 0);
    }

    #[test]
    fn pcf_union() {
        {
            let first = PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            });
            let second = PCF::default();
            assert_eq!(first, first.union(&second));
            assert_eq!(first, second.union(&first));
        }
        {
            let first = PCF::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            });
            let second = PCF::from(vec![
                Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![],
                }
                .into(),
            ]);
            let expected = PCF::from(vec![
                Atom {
                    predicate: "P".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "Q".into(),
                    terms: vec![],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![],
                }
                .into(),
            ]);
            assert_eq!(expected, first.union(&second));
            assert_eq!(expected, second.union(&first));
        }
    }

    #[test]
    fn pcf_free_vars() {
        {
            let pcf = PCF::default();
            assert_eq!(Vec::<&Var>::new(), pcf.free_vars());
        }
        {
            let pcf = PCF::from(vec![
                Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![term!(@c), term!(y)],
                }
                .into(),
                Atom {
                    predicate: "R".into(),
                    terms: vec![term!(x)],
                }
                .into(),
            ]);
            assert_eq_sorted_vecs!([v!(x), v!(y)].iter().collect_vec(), pcf.free_vars());
        }
    }

    #[test]
    fn pcf_transform() {
        {
            let pcf: PCF = Atomic::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(y)],
            })
            .into();
            let f = |t: &Complex| {
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
            };
            assert_eq!(
                PCF::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z), term!(y)],
                }),
                pcf.transform_term(&f)
            );
        }
        {
            let pcf: PCF = Equals {
                left: term!(f(x)),
                right: term!(y),
            }
            .into();
            let f = |t: &Complex| {
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
            };
            assert_eq!(
                PCF::from(Equals {
                    left: term!(z),
                    right: term!(y),
                }),
                pcf.transform_term(&f)
            );
        }
    }

    #[test]
    fn pcf_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: "P".into(),
                arity: 1,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: "Q".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: EQ_SYM.into(),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: "f".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_constant("c".into());

            let pcf = PCF::from(vec![
                Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                Equals {
                    left: term!(f(x, @c)),
                    right: term!(y),
                }
                .into(),
                Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(f(x, y)), term!(x)],
                }
                .into(),
            ]);
            assert_eq!(sig, pcf.signature().unwrap());
        }
        {
            let pcf = PCF::from(vec![
                Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }
                .into(),
                Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .into(),
            ]);
            assert!(pcf.signature().is_err());
        }
    }
}
