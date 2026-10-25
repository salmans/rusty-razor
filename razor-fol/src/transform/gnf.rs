/*! Defines formulae in Geometric Normal Form (GNF), standard geometric sequents, and implements
a conversion from first-order formulae to [`GNF`] sequents.

A *standard geometric sequent* has a body that is a conjunction of atoms and a head that is a
disjunction of existentially quantified conjunctions of atoms; its variables are universally
quantified. Every geometric sequent is equivalent to a set of standard ones (Vickers,
[*Geometric Logic in Computer Science*][glics]).

The conversion of a formula returns a set of standard sequents that is equivalent to it when no
existential is removed, and equisatisfiable to it otherwise. An existential whose scope is
positive-existential (built from atoms, `⊤`, `⊥`, `∧`, `∨` and `∃`) stays in its head. Any other
existential is removed by a [`Geometrization`] policy, which introduces a symbol over the
universals that its scope depends on:

- [`Geometrization::Skolemize`] introduces a Skolem function, or a Skolem constant when the scope
  depends on no universal (Skolemization; Skolem, *Logisch-kombinatorische Untersuchungen über
  die Erfüllbarkeit oder Beweisbarkeit mathematischer Sätze*, 1920). Functions are partial in
  the chase, so a Skolem term that is a constant or occurs in a body comes with a *totality*
  claim `⊢ ∃y. y = t`.
- [`Geometrization::Define`] introduces a predicate over those universals and the existential,
  claims that it holds of some element in place of the existential, and defines it by the
  sequents of its scope (definitional geometrisation; Dyckhoff and Negri, *Geometrisation of
  first-order logic*, Bull. Symbolic Logic 21(2), 2015). It never claims totality.
- [`Geometrization::Hybrid`] Skolemizes where the Skolem term would occur only in heads, and
  defines everywhere else.

A quantifier whose variable does not occur in its scope is vacuous and is removed.

[glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
*/
use super::{ToNNF, ToSNF, CNF, NNF, PNF, SNF};
use crate::syntax::{
    formula::{
        clause::{Clause, Literal},
        *,
    },
    term::Complex,
    Const, Error, Func, Pred, Sig, Term, Var, FOF,
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

impl TryFrom<FOF> for PCF {
    type Error = super::Error;

    fn try_from(value: FOF) -> Result<Self, Self::Error> {
        match value {
            FOF::Top => Ok(Self::default()),
            FOF::Atom(atom) => Ok(Self::from(atom)),
            FOF::Equals(equals) => Ok(Self::from(equals)),
            FOF::And(and) => {
                let mut result = Self::try_from(and.left)?.into_literals();
                result.extend(Self::try_from(and.right)?.into_literals());
                Ok(result.into_iter().collect())
            }
            _ => Err(Self::Error::FofToGnf {
                formula: value.clone(),
            }),
        }
    }
}

#[cfg(test)]
impl PCF {
    // The disjuncts of a disjunction of conjunctions of atoms: none for `⊥`.
    pub(crate) fn disjuncts(formula: FOF) -> Vec<Self> {
        match formula {
            FOF::Bottom => Vec::new(),
            FOF::Or(this) => [Self::disjuncts(this.left), Self::disjuncts(this.right)].concat(),
            _ => vec![Self::try_from(formula).unwrap()],
        }
    }
}

/// Is a disjunct in the head of a [`GNF`] sequent: a list of existentially quantified
/// variables over a conjunction of atoms.
///
/// The existentials of a disjunct are pairwise distinct, distinct from the variables of its
/// sequent, and each occurs in the atoms; a disjunct without atoms keeps a single existential,
/// claiming that an element exists. A disjunct with existentials records the variables of its
/// sequent in scope at its existential quantifier, in binding order, from which
/// [`GNF::dependencies`] takes the arguments of their witnesses.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Disjunct {
    existentials: Vec<Var>,
    scope: Vec<Var>,
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

    // The conjunction of `self` and `other`, whose scope the enclosing `exists` records.
    fn and(&self, other: &Self) -> Self {
        Self {
            existentials: [self.existentials.clone(), other.existentials.clone()].concat(),
            scope: Vec::new(),
            atoms: self.atoms.union(&other.atoms),
        }
    }

    // Is `∃variables. self` where `universals` are the sequent's variables in scope, in binding
    // order.
    fn exists(self, variables: &[Var], universals: &[Var]) -> Self {
        Self {
            existentials: [variables.to_vec(), self.existentials].concat(),
            scope: universals.to_vec(),
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
        let scope = if existentials.is_empty() {
            Vec::new()
        } else {
            self.scope
        };
        Self {
            existentials,
            scope,
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
            scope: self.scope,
            atoms: self.atoms.substitute(&substitution),
        }
    }
}

impl From<Atomic<Complex>> for Disjunct {
    fn from(value: Atomic<Complex>) -> Self {
        Self {
            existentials: Vec::new(),
            scope: Vec::new(),
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
            scope: self.scope.clone(),
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

/// Represents a standard geometric sequent: a body that is a conjunction of atoms over the
/// sequent's variables, implying a head that is a disjunction of [`Disjunct`]s. The sequent's variables are universally quantified; an empty head is `⊥`.
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

    /// Returns the arguments of the witnesses of the existentials of `disjunct`, a disjunct of
    /// the head of `self`: the variables of `self` that were in scope at their quantifier, in
    /// binding order. The chase names a witness `f(x̄)` over the free variables of the sequent,
    /// so every trigger has its own witnesses; a variable the conversion bound inside the
    /// existential's scope is not among them.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToGNF;
    ///
    /// let dependencies = |text: &str| -> Vec<String> {
    ///     let formula: FOF = text.parse().unwrap();
    ///     let sequent = &formula.gnf()[0];
    ///     let disjunct = &sequent.head()[0];
    ///     sequent.dependencies(disjunct).iter().map(|v| v.to_string()).collect()
    /// };
    /// assert_eq!(vec!["x"], dependencies("P(x) -> exists y. Q(y)"));
    /// // `R(y) → ∃ z. Q(z)`: `y` is bound inside the scope of `∃ z`.
    /// assert!(dependencies("exists z. Q(z) | forall y. ~R(y)").is_empty());
    /// ```
    pub fn dependencies(&self, disjunct: &Disjunct) -> Vec<Var> {
        let free = self.free_vars();
        disjunct
            .scope
            .iter()
            .filter(|v| free.contains(v))
            .cloned()
            .collect()
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

    // Returns the claim `⊢ ∃y. y = term` where `universals` are in scope.
    fn total(term: Complex, y: Var, universals: &[Var]) -> Self {
        let equation = Atomic::from(Equals {
            left: Complex::from(y.clone()),
            right: term,
        });
        Self {
            body: PCF::default(),
            head: vec![Disjunct::from(equation).exists(&[y], universals)],
        }
    }

    // Does `term` occur in a body of `sequents`?
    fn mention(sequents: &[Self], term: &Complex) -> bool {
        sequents
            .iter()
            .any(|s| s.body.iter().any(|atomic| atomic.mentions(term)))
    }

    // Returns the sequent of a CNF clause: its negative literals form the body, and each
    // positive literal is a disjunct of the head.
    fn clause(clause: &Clause<Complex>) -> Self {
        let (body, head): (Vec<_>, Vec<_>) = clause.iter().partition_map(|literal| match literal {
            Literal::Neg(atomic) => itertools::Either::Left(atomic.clone()),
            Literal::Pos(atomic) => itertools::Either::Right(Disjunct::from(atomic.clone())),
        });
        Self {
            body: body.into(),
            head,
        }
    }

    // The Skolem terms of `skolemizer` that are constants of `clause` or occur in its negative
    // literals.
    fn skolem_terms<'c>(
        clause: &'c Clause<Complex>,
        skolemizer: &'c Skolemizer,
    ) -> impl Iterator<Item = &'c Complex> {
        clause
            .iter()
            .flat_map(|literal| {
                let (atomic, negative) = match literal {
                    Literal::Neg(atomic) => (atomic, true),
                    Literal::Pos(atomic) => (atomic, false),
                };
                atomic
                    .terms()
                    .into_iter()
                    .flat_map(Complex::subterms)
                    .filter(move |t| negative || matches!(t, Complex::Const(_)))
            })
            .filter(|t| skolemizer.is_skolem(t))
    }

    // Returns the claim `⊤ ⊢ ∃y. y = term` over the variables of `term`.
    fn totality(term: Complex) -> Self {
        let variables: Vec<Var> = term.vars().into_iter().cloned().collect();
        let y = Names::new(&variables).fresh(&Var::from("y"));
        Self::total(term, y, &variables)
    }

    // Returns `self` with `atomic` conjoined to its body.
    fn assume(self, atomic: Atomic<Complex>) -> Self {
        Self {
            body: self.body.union(&atomic.into()),
            head: self.head,
        }
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
        let merged = Self {
            body: self.body.union(&other.body),
            head: self
                .head
                .iter()
                .chain(&other.head)
                .unique()
                .cloned()
                .collect(),
        };
        debug_assert!(merged.is_apart(), "an existential captures in {}", merged);
        merged
    }

    // Are the existentials of `self` distinct from its variables?
    fn is_apart(&self) -> bool {
        let variables = self.free_vars();
        self.head
            .iter()
            .flat_map(Disjunct::existentials)
            .all(|e| !variables.contains(&e))
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
    /// Is similar to [`ToGNF::gnf`] but removes the existentials whose scope is not
    /// positive-existential by `policy`, naming the symbols it introduces by `symbols`. One
    /// [`Symbols`] shared by every formula of a theory keeps those symbols apart.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::{Geometrization, Symbols, ToGNF};
    ///
    /// let first: FOF = "exists x. forall y. P(x, y)".parse().unwrap();
    /// let second: FOF = "exists x. forall y. Q(x, y)".parse().unwrap();
    ///
    /// let skolemize = Geometrization::Skolemize;
    /// let mut symbols = Symbols::default();
    /// assert_eq!("⊤ → P('c#0, y)", first.gnf_with(skolemize, &mut symbols)[0].to_string());
    /// assert_eq!("⊤ → Q('c#1, y)", second.gnf_with(skolemize, &mut symbols)[0].to_string());
    ///
    /// let define = Geometrization::Define;
    /// let mut symbols = Symbols::default();
    /// assert_eq!("⊤ → (∃ x. p#0(x))", first.gnf_with(define, &mut symbols)[0].to_string());
    /// assert_eq!("p#1(x) → Q(x, y)", second.gnf_with(define, &mut symbols)[1].to_string());
    /// ```
    fn gnf_with(&self, policy: Geometrization, symbols: &mut Symbols) -> Vec<GNF>;

    /// Transforms `self` to a list of standard geometric sequents whose conjunction is
    /// equisatisfiable to `self`, and equivalent to it when no existential needs removing. The
    /// free variables of `self` are read as universally quantified, and existentials are
    /// removed by the default [`Geometrization`] with fresh [`Symbols`].
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
        self.gnf_with(Geometrization::default(), &mut Symbols::default())
    }
}

/// How an existential whose scope is not positive-existential is removed.
///
/// Neither `Skolemize` nor `Define` subsumes the other. A Skolem term in a body needs a totality
/// claim, which a definition does without. A definition's claim `∃y. p(x̄, y)` holds for every
/// `x̄`, while a Skolem term only in heads denotes an element only where a head asks for it, so
/// a theory like `∀x ∃y. ((P(x) → Q(y)) ∧ (R(x) → S(y)))` makes the chase create elements
/// without end under `Define` and not under `Skolemize`. `Hybrid` takes the better of the two
/// for each existential.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Geometrization {
    /// Replace the existential by a Skolem term over the universals its scope depends on, and
    /// claim the term's totality where it is a constant or occurs in a body.
    Skolemize,
    /// Name the scope by a fresh predicate over those universals and the existential, claim
    /// that the predicate holds of some element, and define it by the scope.
    Define,
    /// Skolemize where the Skolem term would occur only in heads, and define elsewhere. The
    /// default: it terminates wherever `Skolemize` does and never needs a totality claim.
    #[default]
    Hybrid,
}

/// Names the symbols that the conversion of a theory to geometric form introduces: Skolem
/// constants `c#N` and functions `f#N`, and the predicates `p#N` that name the scopes of
/// existentials, each numbered in the order it is introduced. `#` is not an identifier
/// character, so an introduced symbol never collides with a parsed one. Models are reported as
/// the reduct to the theory's signature, so the predicates are not user-visible.
#[derive(Clone, Debug, Default)]
pub struct Symbols {
    skolemizer: Skolemizer,
    definitions: Definitions,
}

// Introduces the Skolem constants and functions of a theory, and records them, so that the
// conversion of a Skolemized clause knows its Skolem terms.
#[derive(Clone, Debug, Default)]
struct Skolemizer {
    constants: Vec<Const>,
    functions: Vec<Func>,
}

impl Skolemizer {
    fn constant(&mut self) -> Const {
        let constant: Const = format!("c#{}", self.constants.len()).into();
        self.constants.push(constant.clone());
        constant
    }

    fn function(&mut self) -> Func {
        let function: Func = format!("f#{}", self.functions.len()).into();
        self.functions.push(function.clone());
        function
    }

    // A function applied to `universals`, or a constant when there are none.
    fn term(&mut self, universals: &[Var]) -> Complex {
        if universals.is_empty() {
            self.constant().into()
        } else {
            self.function()
                .app(universals.iter().map(Complex::from).collect())
        }
    }

    // Is `term` a constant or an application of a function that `self` introduced?
    fn is_skolem(&self, term: &Complex) -> bool {
        match term {
            Complex::Var(_) => false,
            Complex::Const(constant) => self.constants.contains(constant),
            Complex::App { function, .. } => self.functions.contains(function),
        }
    }
}

// Introduces the predicates of a theory that name the scopes of existentials.
#[derive(Clone, Debug, Default)]
struct Definitions {
    predicates: usize,
}

impl Definitions {
    fn predicate(&mut self) -> Pred {
        self.predicates += 1;
        format!("p#{}", self.predicates - 1).into()
    }
}

// The number of symbols of each kind a [`Symbols`] has introduced, to which a trial returns it.
struct Introduced {
    constants: usize,
    functions: usize,
    predicates: usize,
}

impl Symbols {
    /// The number of Skolem constants introduced so far, `c#0` to `c#N-1`.
    pub fn constants(&self) -> usize {
        self.skolemizer.constants.len()
    }

    /// The number of Skolem functions introduced so far, `f#0` to `f#N-1`.
    pub fn functions(&self) -> usize {
        self.skolemizer.functions.len()
    }

    fn introduced(&self) -> Introduced {
        Introduced {
            constants: self.constants(),
            functions: self.functions(),
            predicates: self.definitions.predicates,
        }
    }

    fn forget(&mut self, introduced: Introduced) {
        self.skolemizer.constants.truncate(introduced.constants);
        self.skolemizer.functions.truncate(introduced.functions);
        self.definitions.predicates = introduced.predicates;
    }
}

impl ToGNF for NNF {
    fn gnf_with(&self, policy: Geometrization, symbols: &mut Symbols) -> Vec<GNF> {
        Converter::convert(policy, symbols, self)
    }
}

/// Simplifies the formula ([`FOF::simplify`]) and converts it through [`NNF`].
impl ToGNF for FOF {
    fn gnf_with(&self, policy: Geometrization, symbols: &mut Symbols) -> Vec<GNF> {
        self.simplify().nnf().gnf_with(policy, symbols)
    }
}

/// Converts every clause to one sequent: its negative
/// literals form the body and its positive literals the disjuncts of the head, with no
/// existentials. A [`CNF`] has no existential, so the policy is never consulted.
///
/// Functions are partial in the chase, so a Skolem symbol that is a constant or occurs in a
/// negative literal of some clause also yields one totality claim `⊤ ⊢x̄ ∃y. y = f(x̄)` over the
/// variables of its term. A [`CNF`] keeps no quantifier structure to condition the claim on, so
/// the classical route makes such a Skolem symbol total over the whole domain, wherever any
/// body mentions it, unlike the direct route through [`NNF`], which claims a term only where its
/// existential must hold. Total Skolem functions make the chase create elements the theory does
/// not ask for, which is why Razor converts by the direct route. The Skolem symbols are those
/// `symbols` introduced, so a [`CNF`] gets its claims only when it was Skolemized by `symbols`,
/// as [`ToGNF::gnf_with`] on a [`PNF`] under [`Geometrization::Skolemize`] does with the symbols
/// of a whole theory. **Warning**: a [`CNF`] made by [`ToCNF::cnf`](super::ToCNF::cnf) names its
/// own Skolem symbols, numbered apart from no other formula, and [`ToGNF::gnf`] gets no claims
/// for them.
///
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::FOF;
/// use razor_fol::transform::{Geometrization, Symbols, ToGNF, ToPNF};
///
/// let formula: FOF = "exists y. ~R(y)".parse().unwrap();
/// let mut symbols = Symbols::default();
/// let sequents = formula.pnf().gnf_with(Geometrization::Skolemize, &mut symbols);
///
/// assert_eq!("R('c#0) → ⟘", sequents[0].to_string());
/// assert_eq!("⊤ → (∃ y. y = 'c#0)", sequents[1].to_string());
/// ```
impl ToGNF for CNF {
    fn gnf_with(&self, _: Geometrization, symbols: &mut Symbols) -> Vec<GNF> {
        let claims = self
            .iter()
            .flat_map(|clause| GNF::skolem_terms(clause, &symbols.skolemizer))
            .unique_by(|term| match term {
                Complex::Var(variable) => variable.name(),
                Complex::Const(constant) => constant.name(),
                Complex::App { function, .. } => function.name(),
            })
            .cloned()
            .map(GNF::totality);
        self.iter()
            .map(GNF::clause)
            .chain(claims)
            .unique()
            .collect()
    }
}

/// Converts through [`CNF`]: see the conversion of a [`CNF`].
impl ToGNF for SNF {
    fn gnf_with(&self, policy: Geometrization, symbols: &mut Symbols) -> Vec<GNF> {
        use super::ToCNF;
        self.cnf().gnf_with(policy, symbols)
    }
}

/// Under [`Geometrization::Skolemize`], Skolemizes every existential by `symbols` and converts
/// through [`SNF`]. A prenex existential has no scope left to name, so under any other policy
/// the formula takes the direct route through [`NNF`].
impl ToGNF for PNF {
    fn gnf_with(&self, policy: Geometrization, symbols: &mut Symbols) -> Vec<GNF> {
        if policy != Geometrization::Skolemize {
            return FOF::from(self).nnf().gnf_with(policy, symbols);
        }
        let skolemizer = RefCell::new(&mut symbols.skolemizer);
        let snf = self.snf_with(&mut || skolemizer.borrow_mut().constant(), &mut || {
            skolemizer.borrow_mut().function()
        });
        snf.gnf_with(policy, symbols)
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

    // The universals in scope, in binding order, that occur free in `∃variables. formula`: the
    // variables a removal of that existential depends on.
    fn dependencies(&self, variables: &[Var], formula: &NNF) -> Vec<Var> {
        let occurring: HashSet<&Var> = formula
            .free_vars()
            .into_iter()
            .filter(|v| !variables.contains(v))
            .flat_map(|v| match self.env.get(v) {
                Some(term) => term.vars(),
                None => vec![v],
            })
            .collect();
        self.universals
            .iter()
            .filter(|u| occurring.contains(u))
            .cloned()
            .collect()
    }
}

// The variables of the conversion of one formula. Every variable it binds, universal or
// existential, is named apart from all of them, so sequents and disjuncts combine without
// renaming and no binder captures another's variable.
struct Names {
    taken: HashSet<Var>,
    // The names `fresh` returned, in order, so a trial can be undone.
    trail: Vec<Var>,
}

impl Names {
    // The names of a formula whose free variables are `free`.
    fn new(free: &[Var]) -> Self {
        Self {
            taken: free.iter().cloned().collect(),
            trail: Vec::new(),
        }
    }

    // Returns `variable` with backticks appended until it is not taken, and takes it.
    fn fresh(&mut self, variable: &Var) -> Var {
        let mut name = variable.clone();
        while self.taken.contains(&name) {
            name = format!("{}`", name.name()).into();
        }
        self.taken.insert(name.clone());
        self.trail.push(name.clone());
        name
    }

    fn mark(&self) -> usize {
        self.trail.len()
    }

    // Releases the names taken since `mark`.
    fn undo(&mut self, mark: usize) {
        for name in self.trail.drain(mark..) {
            self.taken.remove(&name);
        }
    }
}

// Converts a formula outside every existential quantifier.
struct Converter<'s> {
    policy: Geometrization,
    symbols: &'s mut Symbols,
    // The sequents defining the predicates introduced so far: a definition holds outside every
    // enclosing disjunction.
    defining: Vec<GNF>,
    names: Names,
    // Whether the trial Skolemization of a scope, by address, needed no totality claim.
    trials: HashMap<*const NNF, bool>,
}

// The state of a [`Converter`] before a trial, which undoing the trial restores.
struct Mark {
    symbols: Introduced,
    defining: usize,
    names: usize,
}

impl<'s> Converter<'s> {
    fn convert(policy: Geometrization, symbols: &'s mut Symbols, formula: &NNF) -> Vec<GNF> {
        let universals: Vec<Var> = formula.free_vars().into_iter().cloned().collect();
        let mut converter = Self {
            policy,
            symbols,
            defining: Vec::new(),
            names: Names::new(&universals),
            trials: HashMap::new(),
        };
        let scope = Scope {
            universals,
            env: HashMap::new(),
        };
        let mut sequents = converter.sequents(formula, &scope);
        sequents.extend(converter.defining);
        sequents.into_iter().unique().collect()
    }

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
        let mark = self.names.mark();
        if let Some(disjuncts) = Block(&mut self.names).exists(&variables, formula, scope) {
            return GNF::claim(disjuncts);
        }
        self.names.undo(mark);
        match formula {
            NNF::Or(this) => {
                let left = self.exists(variables.clone(), &this.left, scope);
                let right = self.exists(variables, &this.right, scope);
                GNF::or(&left, &right)
            }
            _ => {
                let referenced = Self::referenced(&variables, formula);
                if referenced.is_empty() {
                    self.sequents(formula, scope)
                } else {
                    let context = scope.dependencies(&referenced, formula);
                    self.remove(&referenced, &context, formula, scope)
                }
            }
        }
    }

    // Returns the sequents of `∃variables. formula`, where `formula` refers to every variable
    // and depends on the universals `context`.
    fn remove(
        &mut self,
        variables: &[Var],
        context: &[Var],
        formula: &NNF,
        scope: &Scope,
    ) -> Vec<GNF> {
        match self.policy {
            Geometrization::Skolemize => {
                let (mut sequents, claims) = self.skolemize(variables, context, formula, scope);
                sequents.extend(claims);
                sequents
            }
            Geometrization::Define => self.define(variables, context, formula, scope),
            Geometrization::Hybrid if context.is_empty() => {
                self.define(variables, context, formula, scope)
            }
            Geometrization::Hybrid => match self.trials.get(&(formula as *const NNF)) {
                Some(true) => {
                    let (mut sequents, claims) = self.skolemize(variables, context, formula, scope);
                    sequents.extend(claims);
                    sequents
                }
                Some(false) => self.define(variables, context, formula, scope),
                None if formula.skolemizes_lazily(variables) => {
                    let (sequents, claims) = self.skolemize(variables, context, formula, scope);
                    debug_assert!(claims.is_empty(), "a lazy Skolemization claimed totality");
                    sequents
                }
                None => self.trial(variables, context, formula, scope),
            },
        }
    }

    // Skolemizes `variables` when no totality claim is needed, and defines `formula` otherwise,
    // undoing the Skolemization. Either way the decision is recorded for `formula`: converting
    // the definition of an enclosing scope converts `formula` again, and deciding it afresh
    // there would double the work at every level of nesting.
    fn trial(
        &mut self,
        variables: &[Var],
        context: &[Var],
        formula: &NNF,
        scope: &Scope,
    ) -> Vec<GNF> {
        let mark = self.mark();
        let (sequents, claims) = self.skolemize(variables, context, formula, scope);
        let lazy = claims.is_empty();
        self.trials.insert(formula, lazy);
        if lazy {
            sequents
        } else {
            self.undo(mark);
            self.define(variables, context, formula, scope)
        }
    }

    fn mark(&self) -> Mark {
        Mark {
            symbols: self.symbols.introduced(),
            defining: self.defining.len(),
            names: self.names.mark(),
        }
    }

    fn undo(&mut self, mark: Mark) {
        self.symbols.forget(mark.symbols);
        self.defining.truncate(mark.defining);
        self.names.undo(mark.names);
    }

    // Returns the sequents of `formula` with every variable replaced by a Skolem term over
    // `context`, and separately the totality claims of the terms that are constants or occur in
    // a body of those sequents or of the definitions their conversion added.
    fn skolemize(
        &mut self,
        variables: &[Var],
        context: &[Var],
        formula: &NNF,
        scope: &Scope,
    ) -> (Vec<GNF>, Vec<GNF>) {
        let mut inner = scope.clone();
        let mut terms = Vec::new();
        for v in variables {
            let term = self.symbols.skolemizer.term(context);
            terms.push(term.clone());
            inner = inner.bind(v, term);
        }
        let defined = self.defining.len();
        let sequents = self.sequents(formula, &inner);
        let emitted = &self.defining[defined..];
        let claimed: Vec<Complex> = terms
            .into_iter()
            .filter(|t| {
                matches!(t, Complex::Const(_))
                    || GNF::mention(&sequents, t)
                    || GNF::mention(emitted, t)
            })
            .collect();
        let claims = claimed
            .into_iter()
            .map(|t| GNF::total(t, self.names.fresh(&Var::from("y")), &scope.universals))
            .collect();
        (sequents, claims)
    }

    // Returns the claim `∃variables. p(context, variables)` for a fresh predicate `p`, and
    // records the sequents of `p(context, variables) ⊢ formula`.
    fn define(
        &mut self,
        variables: &[Var],
        context: &[Var],
        formula: &NNF,
        scope: &Scope,
    ) -> Vec<GNF> {
        let inner = variables
            .iter()
            .fold(scope.clone(), |inner, v| self.universal(v, &inner));
        let existentials = &inner.universals[scope.universals.len()..];
        let name = Atomic::from(Atom {
            predicate: self.symbols.definitions.predicate(),
            terms: context
                .iter()
                .chain(existentials)
                .map(Complex::from)
                .collect(),
        });
        let definition: Vec<GNF> = self
            .sequents(formula, &inner)
            .into_iter()
            .map(|sequent| sequent.assume(name.clone()))
            .collect();
        self.defining.extend(definition);
        GNF::claim(vec![Disjunct::from(name)
            .exists(existentials, &scope.universals)
            .simplify()])
    }

    // The variables of `variables` that `formula` refers to; the last binding of a repeated
    // variable shadows the others.
    fn referenced(variables: &[Var], formula: &NNF) -> Vec<Var> {
        let free = formula.free_vars();
        variables
            .iter()
            .enumerate()
            .filter(|(i, v)| free.contains(v) && !variables[i + 1..].contains(v))
            .map(|(_, v)| v.clone())
            .collect()
    }

    fn universal(&mut self, variable: &Var, scope: &Scope) -> Scope {
        scope.universal(variable, self.names.fresh(variable))
    }
}

// Converts the scope of an existential quantifier into disjuncts if it is a positive-existential
// formula, taking fresh names for its existentials.
struct Block<'n>(&'n mut Names);

impl Block<'_> {
    fn exists(&mut self, variables: &[Var], formula: &NNF, scope: &Scope) -> Option<Vec<Disjunct>> {
        let mut scope = scope.clone();
        let mut names = Vec::new();
        for variable in variables {
            let name = self.0.fresh(variable);
            scope = scope.bind(variable, name.clone().into());
            names.push(name);
        }
        let disjuncts = self.disjuncts(formula, &scope)?;
        Some(
            disjuncts
                .into_iter()
                .map(|d| d.exists(&names, &scope.universals).simplify())
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

trait NnfEx {
    // Is `self` positive-existential?
    fn is_positive(&self) -> bool;

    // Does Skolemizing `variables` in the scope `self` put their terms in no body? Only a
    // negative literal moves atoms to a body, and only a nested scope that is not a PEF adds
    // definitions, whose bodies may mention them.
    fn skolemizes_lazily(&self, variables: &[Var]) -> bool;
}

impl NnfEx for NNF {
    fn is_positive(&self) -> bool {
        match self {
            NNF::Top | NNF::Bottom | NNF::Literal(Literal::Pos(_)) => true,
            NNF::Literal(Literal::Neg(_)) | NNF::Forall(_) => false,
            NNF::And(this) => this.left.is_positive() && this.right.is_positive(),
            NNF::Or(this) => this.left.is_positive() && this.right.is_positive(),
            NNF::Exists(this) => this.formula.is_positive(),
        }
    }

    fn skolemizes_lazily(&self, variables: &[Var]) -> bool {
        match self {
            NNF::Top | NNF::Bottom | NNF::Literal(Literal::Pos(_)) => true,
            NNF::Literal(Literal::Neg(atomic)) => {
                !atomic.free_vars().iter().any(|v| variables.contains(v))
            }
            NNF::And(this) => {
                this.left.skolemizes_lazily(variables) && this.right.skolemizes_lazily(variables)
            }
            NNF::Or(this) => {
                this.left.skolemizes_lazily(variables) && this.right.skolemizes_lazily(variables)
            }
            NNF::Forall(this) => this.formula.skolemizes_lazily(variables),
            NNF::Exists(this) => this.formula.is_positive(),
        }
    }
}

trait ComplexEx {
    fn contains(&self, term: &Complex) -> bool;

    // `self` and the terms nested in it.
    fn subterms(&self) -> Vec<&Complex>;
}

impl ComplexEx for Complex {
    fn contains(&self, term: &Complex) -> bool {
        self == term
            || matches!(self, Complex::App { terms, .. } if terms.iter().any(|t| t.contains(term)))
    }

    fn subterms(&self) -> Vec<&Complex> {
        let nested = match self {
            Complex::App { terms, .. } => terms.iter().flat_map(Complex::subterms).collect(),
            Complex::Var(_) | Complex::Const(_) => Vec::new(),
        };
        [vec![self], nested].concat()
    }
}

trait AtomicEx {
    fn is_reflexive(&self) -> bool;

    // The terms `self` applies its predicate or equation to.
    fn terms(&self) -> Vec<&Complex>;

    fn mentions(&self, term: &Complex) -> bool;

    fn variable_equation(&self) -> Option<(&Var, &Var)>;
}

impl AtomicEx for Atomic<Complex> {
    fn is_reflexive(&self) -> bool {
        matches!(self.variable_equation(), Some((left, right)) if left == right)
    }

    fn terms(&self) -> Vec<&Complex> {
        match self {
            Atomic::Atom(this) => this.terms.iter().collect(),
            Atomic::Equals(this) => vec![&this.left, &this.right],
        }
    }

    fn mentions(&self, term: &Complex) -> bool {
        self.terms().iter().any(|t| t.contains(term))
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
        term,
        transform::{ToCNF, ToPNF},
        v,
    };
    use std::{fs, path::PathBuf};

    // Converts `text` and prints one sequent per line.
    fn gnf(text: &str) -> String {
        let formula: FOF = text.parse().unwrap();
        formula.gnf().iter().join("\n")
    }

    // Converts `text` under `Skolemize` and prints one sequent per line.
    fn skolemize(text: &str) -> String {
        let formula: FOF = text.parse().unwrap();
        formula
            .gnf_with(Geometrization::Skolemize, &mut Symbols::default())
            .iter()
            .join("\n")
    }

    // Converts `text` under `Hybrid` and prints one sequent per line.
    fn hybrid(text: &str) -> String {
        let formula: FOF = text.parse().unwrap();
        formula
            .gnf_with(Geometrization::Hybrid, &mut Symbols::default())
            .iter()
            .join("\n")
    }

    // Converts `text` under `Define` and prints one sequent per line.
    fn define(text: &str) -> String {
        let formula: FOF = text.parse().unwrap();
        formula
            .gnf_with(Geometrization::Define, &mut Symbols::default())
            .iter()
            .join("\n")
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

    // The dependencies of every disjunct of every sequent of `text`.
    fn dependencies(text: &str) -> Vec<Vec<Var>> {
        let formula: FOF = text.parse().unwrap();
        formula
            .gnf()
            .iter()
            .flat_map(|g| g.head().iter().map(|d| g.dependencies(d)))
            .collect()
    }

    #[test]
    fn a_dependency_was_in_scope_at_the_existential() {
        assert_eq!(
            vec![vars(&["x"])],
            dependencies("forall x. (P(x) -> (exists z. Q(z) | forall y. ~R(y, x)))")
        );
        assert_eq!(
            vec![vars(&["x", "u"])],
            dependencies("P(x) & R(u) -> exists z. (Q(x, z) | forall y. ~R(y))")
        );
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
            skolemize("exists y. forall u. Q(u, y)")
        );
    }

    #[test]
    fn exists_over_negative_literal_is_skolemized_over_universals() {
        assert_eq!(
            "⊤ → P(x, f#0(x))\nQ(f#0(x)) → R(f#0(x))\n⊤ → (∃ y. y = f#0(x))",
            skolemize("forall x. exists y. (P(x, y) & (Q(y) -> R(y)))")
        );
    }

    #[test]
    fn a_skolem_term_only_in_a_body_is_total() {
        assert_eq!(
            "P('c#0) → (∃ z. Q(z))\n⊤ → ((∃ y. y = 'c#0) ∨ (∃ z. Q(z)))",
            skolemize("exists z. (P(z) -> Q(z))")
        );
    }

    #[test]
    fn totality_names_its_existential_apart_from_the_universals() {
        assert_eq!(
            "Q(y, f#0(y)) → ⟘\n⊤ → (∃ y`. y` = f#0(y))",
            skolemize("forall y. exists z. ~Q(y, z)")
        );
    }

    #[test]
    fn totality_names_its_existential_apart_from_a_sibling_universal() {
        assert_eq!(
            "P('c#0) → Q(y`)\n⊤ → ((∃ y. y = 'c#0) ∨ Q(y`))",
            skolemize("(exists z. ~P(z)) | forall y. Q(y)")
        );
    }

    #[test]
    fn totality_is_claimed_where_the_existential_must_hold() {
        assert_eq!(
            "⊤ → (P('a) ∨ Q('c#0, u))\n⊤ → (P('a) ∨ (∃ y. y = 'c#0))",
            skolemize("P('a) | exists z. forall u. Q(z, u)")
        );
        assert_eq!(
            "(P(x) ∧ Q(x, f#0(x))) → ⟘\nP(x) → (∃ y. y = f#0(x))",
            skolemize("forall x. (P(x) -> exists z. ~Q(x, z))")
        );
    }

    #[test]
    fn a_skolem_function_only_in_heads_is_not_claimed() {
        assert_eq!(
            "P(x) → Q(f#0(x))\nR(x) → S(f#0(x))",
            skolemize("forall x. exists y. ((P(x) -> Q(y)) & (R(x) -> S(y)))")
        );
    }

    #[test]
    fn exists_skolemizes_only_the_non_positive_disjunct() {
        assert_eq!(
            "⊤ → ((∃ y. P(y)) ∨ Q(u, 'c#0))\n⊤ → ((∃ y. P(y)) ∨ (∃ y`. y` = 'c#0))",
            skolemize("exists y. (P(y) | forall u. Q(u, y))")
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
    fn one_policy_numbers_the_symbols_of_every_formula() {
        let mut symbols = Symbols::default();
        let first: FOF = "forall x. exists y. ~P(x, y)".parse().unwrap();
        let second: FOF = "exists y. ~Q(y)".parse().unwrap();
        assert_eq!(
            "P(x, f#0(x)) → ⟘\n⊤ → (∃ y. y = f#0(x))",
            first
                .gnf_with(Geometrization::Skolemize, &mut symbols)
                .iter()
                .join("\n")
        );
        assert_eq!(
            "Q('c#0) → ⟘\n⊤ → (∃ y. y = 'c#0)",
            second
                .gnf_with(Geometrization::Skolemize, &mut symbols)
                .iter()
                .join("\n")
        );
    }

    #[test]
    fn define_names_a_scope_over_no_universal() {
        assert_eq!(
            "⊤ → (∃ y. p#0(y))\np#0(y) → Q(u, y)",
            define("exists y. forall u. Q(u, y)")
        );
    }

    #[test]
    fn define_names_a_scope_over_the_universals() {
        assert_eq!(
            "⊤ → (∃ y. p#0(x, y))\np#0(x, y) → P(x, y)\n(Q(y) ∧ p#0(x, y)) → R(y)",
            define("forall x. exists y. (P(x, y) & (Q(y) -> R(y)))")
        );
    }

    #[test]
    fn define_claims_the_scope_where_the_existential_must_hold() {
        assert_eq!(
            "⊤ → P('a)\n⊤ → ((∃ z. p#0(z)) ∨ (∃ z`. Q(z`)))\n(P(z) ∧ p#0(z)) → ⟘",
            define("P('a) & exists z. (P(z) -> Q(z))")
        );
        assert_eq!(
            "P(x) → (∃ z. p#0(x, z))\n(Q(x, z) ∧ p#0(x, z)) → ⟘",
            define("forall x. (P(x) -> exists z. ~Q(x, z))")
        );
        assert_eq!(
            "⊤ → (P('a) ∨ (∃ z. p#0(z)))\np#0(z) → Q(z, u)",
            define("P('a) | exists z. forall u. Q(z, u)")
        );
    }

    #[test]
    fn define_names_nested_scopes_apart() {
        assert_eq!(
            "⊤ → (∃ y. p#0(y))\n(R(z, y) ∧ p#1(y, z)) → ⟘\np#0(y) → ((∃ z. p#1(y, z)) ∨ Q(u, y))",
            define("exists y. forall u. exists z. (R(z, y) -> Q(u, y))")
        );
    }

    #[test]
    fn a_removal_takes_only_the_universals_its_scope_mentions() {
        let text = "forall x. (P(x) -> exists z. ~Q(z))";
        assert_eq!(
            "(P(x) ∧ Q('c#0)) → ⟘\nP(x) → (∃ y. y = 'c#0)",
            skolemize(text)
        );
        assert_eq!("P(x) → (∃ z. p#0(z))\n(Q(z) ∧ p#0(z)) → ⟘", define(text));
    }

    #[test]
    fn a_conjunct_beside_a_removed_scope_differs_between_the_policies() {
        // Under `Skolemize`, `R('b)` on both sides of the disjunction leaves a sequent without
        // `x`, which holds over the empty domain only if `R('b)` does; under `Define` it stays
        // in the definition, whose name keeps `x`.
        let text = "forall x. (R('b) | exists z. (R('b) & 'b = x & ~Q(z)))";
        assert_eq!(
            "⊤ → R('b)\n⊤ → (R('b) ∨ 'b = x)\nQ(f#0(x)) → R('b)\n⊤ → (R('b) ∨ (∃ y. y = f#0(x)))",
            skolemize(text)
        );
        assert_eq!(
            "⊤ → (R('b) ∨ (∃ z. p#0(x, z)))\np#0(x, z) → R('b)\np#0(x, z) → 'b = x\n(Q(z) ∧ p#0(x, z)) → ⟘",
            define(text)
        );
    }

    #[test]
    fn hybrid_skolemizes_a_term_only_in_heads() {
        let text = "forall x. exists y. ((P(x) -> Q(y)) & (R(x) -> S(y)))";
        assert_eq!("P(x) → Q(f#0(x))\nR(x) → S(f#0(x))", hybrid(text));
        assert_eq!(skolemize(text), hybrid(text));
    }

    #[test]
    fn hybrid_defines_a_term_in_a_body() {
        let text = "exists z. (P(z) -> Q(z))";
        assert_eq!(
            "⊤ → ((∃ z. p#0(z)) ∨ (∃ z`. Q(z`)))\n(P(z) ∧ p#0(z)) → ⟘",
            hybrid(text)
        );
        assert_eq!(define(text), hybrid(text));
    }

    #[test]
    fn hybrid_defines_a_constant() {
        let text = "exists y. forall u. Q(u, y)";
        assert_eq!("⊤ → (∃ y. p#0(y))\np#0(y) → Q(u, y)", hybrid(text));
        assert_eq!(define(text), hybrid(text));
    }

    #[test]
    fn hybrid_numbers_only_the_symbols_it_keeps() {
        assert_eq!(
            "⊤ → (∃ z. p#0(x, z))\nP(x) → Q(f#0(x))\nR(x) → S(f#0(x))\n(R(x, z) ∧ p#0(x, z)) → ⟘",
            hybrid(
                "forall x. ((exists z. ~R(x, z)) & exists y. ((P(x) -> Q(y)) & (R(x) -> S(y))))"
            )
        );
    }

    #[test]
    fn hybrid_defines_a_term_a_nested_definition_mentions() {
        assert_eq!(
            "S(x) → (∃ y. p#0(x, y))\n\
             (R(x, y, z) ∧ p#1(x, y, z)) → ⟘\n\
             p#1(x, y, z) → Q(z)\n\
             p#0(x, y) → P(x)\n\
             p#0(x, y) → (∃ z. p#1(x, y, z))",
            hybrid("forall x. (S(x) -> exists y. (P(x) & exists z. (~R(x, y, z) & Q(z))))")
        );
    }

    // `∃y₁ ∀u₁ … ∃yₙ ∀uₙ. (R(x, y₁, …, yₙ) ∨ (¬Q(u₁, y₁) ∧ … ∧ ¬Q(uₙ, yₙ)))`.
    fn nested_removals(n: usize) -> String {
        let ys = (1..=n).map(|i| format!("y{}", i)).join(", ");
        let negations = (1..=n).map(|i| format!("~Q(u{i}, y{i})")).join(" & ");
        let prefix = (1..=n)
            .map(|i| format!("exists y{i}. forall u{i}. "))
            .join("");
        format!("forall x. {}(R(x, {}) | {})", prefix, ys, negations)
    }

    // The time `Hybrid` takes to convert `nested_removals(n)`.
    fn nested_conversion(n: usize) -> std::time::Duration {
        let formula = nested_removals(n).parse::<FOF>().unwrap().nnf();
        let start = std::time::Instant::now();
        formula.gnf();
        start.elapsed()
    }

    #[test]
    fn hybrid_decides_nested_removals_once() {
        // Deciding every level afresh doubles the work per level: 64 times from 6 to 12.
        let shallow = nested_conversion(6);
        let deep = nested_conversion(12);
        assert!(deep < shallow * 16, "{:?} at 6, {:?} at 12", shallow, deep);
    }

    // The conjunction of `conjuncts` as a balanced tree, which a recursive walk can descend.
    fn balanced(mut conjuncts: Vec<FOF>) -> FOF {
        while conjuncts.len() > 1 {
            conjuncts = conjuncts
                .into_iter()
                .chunks(2)
                .into_iter()
                .map(|pair| pair.reduce(FOF::and).unwrap())
                .collect();
        }
        conjuncts.pop().unwrap_or(FOF::Top)
    }

    // The time `Hybrid` takes to convert `n` sibling removals that it defines.
    fn sibling_removals(n: usize) -> std::time::Duration {
        let formula = balanced(
            (0..n)
                .map(|i| {
                    format!("exists y{i}. (P(x, y{i}) & forall u{i}. ~Q(u{i}, y{i}))")
                        .parse()
                        .unwrap()
                })
                .collect(),
        )
        .nnf();
        let start = std::time::Instant::now();
        formula.gnf();
        start.elapsed()
    }

    #[test]
    fn hybrid_converts_sibling_removals_in_linear_time() {
        let small = sibling_removals(200);
        let large = sibling_removals(800);
        assert!(
            large < small * 8,
            "{:?} for 200, {:?} for 800",
            small,
            large
        );
    }

    #[test]
    fn all_policies_agree_on_positive_scopes() {
        for (_, theory) in all_fixtures() {
            for formula in theory.iter() {
                let skolemized =
                    formula.gnf_with(Geometrization::Skolemize, &mut Symbols::default());
                if skolemized.iter().join("\n").contains('#') {
                    continue;
                }
                let defined = formula.gnf_with(Geometrization::Define, &mut Symbols::default());
                assert_eq!(skolemized, defined);
                assert_eq!(
                    skolemized,
                    formula.gnf_with(Geometrization::Hybrid, &mut Symbols::default())
                );
            }
        }
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

    #[test]
    fn pcf_from_conjunction_of_atoms() {
        let pcf = |text: &str| PCF::try_from(text.parse::<FOF>().unwrap());
        assert_eq!(
            "P(x) ∧ x = y",
            FOF::from(pcf("(P(x) & x = y) & true").unwrap()).to_string()
        );
        assert!(pcf("P(x) & (Q(x) | R(x))").is_err());
    }

    // The names of the symbols of `sequents` that the conversion did not introduce.
    fn source_symbols(sequents: &[GNF]) -> BTreeSet<String> {
        sequents
            .iter()
            .flat_map(|sequent| {
                let sig = sequent.signature().unwrap();
                let constants = sig.constants().iter().map(|c| c.to_string());
                let functions = sig.functions().keys().cloned();
                let predicates = sig.predicates().keys().cloned();
                constants.chain(functions).chain(predicates).collect_vec()
            })
            .filter(|name| !name.contains('#'))
            .collect()
    }

    // Converts `text` through the classical route with one `Symbols` for all its formulae.
    fn classical(text: &str) -> String {
        let theory: Theory<FOF> = text.parse().unwrap();
        let mut symbols = Symbols::default();
        theory
            .formulae()
            .iter()
            .flat_map(|f| f.pnf().gnf_with(Geometrization::Skolemize, &mut symbols))
            .join("\n")
    }

    #[test]
    fn classical_route_numbers_skolem_symbols_across_formulae() {
        assert_eq!(
            "⊤ → P('c#0)\n⊤ → (∃ y. y = 'c#0)\nP('c#1) → ⟘\n⊤ → (∃ y. y = 'c#1)",
            classical("exists y. P(y); exists y. ~P(y);")
        );
    }

    #[test]
    fn classical_route_makes_a_skolem_term_in_a_body_total() {
        assert_eq!(
            "⊤ → R('a)\nR('c#0) → ⟘\n⊤ → (∃ y. y = 'c#0)\n⊤ → R(x)",
            classical("R('a); exists y. ~R(y); forall x. R(x);")
        );
        assert_eq!(
            "(Q(x) ∧ R(x, f#0(x))) → S(x)\n⊤ → (∃ y. y = f#0(x))",
            classical("forall x. (Q(x) -> exists z. ~R(x, z) | S(x));")
                .split('\n')
                .sorted()
                .join("\n")
        );
    }

    #[test]
    fn cnf_route_keeps_the_source_signature() {
        let formula: FOF = "P(x) -> exists y. (Q(x, y) & R('c)) | exists z. S(f(z))"
            .parse()
            .unwrap();
        assert_eq!(
            source_symbols(&formula.gnf()),
            source_symbols(&formula.cnf().gnf())
        );
    }

    #[test]
    fn cnf_route_agrees_without_existentials() {
        let formula: FOF =
            "(P(x) & Q(x) -> R(x) | S(x)) & (R(x) -> ~T(x, f(y))) & (P('c) <=> Q(x))"
                .parse()
                .unwrap();
        let sorted = |sequents: Vec<GNF>| sequents.iter().map(GNF::to_string).sorted().join("\n");
        assert_eq!(sorted(formula.gnf()), sorted(formula.cnf().gnf()));
    }
}
