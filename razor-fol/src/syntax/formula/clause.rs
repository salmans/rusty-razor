use super::{Atom, Atomic, Equals, Formula, Not};
use crate::syntax::{Error, Sig, Term, V};
use itertools::Itertools;
use std::{collections::BTreeSet, hash::Hash, ops::Deref};

/// A literal is either an [`Atomic`] formula or its negation.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Literal<T: Term> {
    /// Wraps an (positive) [`Atomic`] formula.
    Pos(Atomic<T>),

    /// Wraps the negation of an [`Atomic`] formula.    
    Neg(Atomic<T>),
}

impl<T: Term> From<Atomic<T>> for Literal<T> {
    fn from(value: Atomic<T>) -> Self {
        Self::Pos(value)
    }
}

impl<T: Term> From<Not<Atomic<T>>> for Literal<T> {
    fn from(value: Not<Atomic<T>>) -> Self {
        Self::Neg(value.formula)
    }
}

impl<T: Term> From<Atom<T>> for Literal<T> {
    fn from(value: Atom<T>) -> Self {
        Self::Pos(value.into())
    }
}

impl<T: Term> From<Not<Atom<T>>> for Literal<T> {
    fn from(value: Not<Atom<T>>) -> Self {
        Self::Neg(value.formula.into())
    }
}

impl<T: Term> From<Equals<T>> for Literal<T> {
    fn from(value: Equals<T>) -> Self {
        Self::Pos(value.into())
    }
}

impl<T: Term> From<Not<Equals<T>>> for Literal<T> {
    fn from(value: Not<Equals<T>>) -> Self {
        Self::Neg(value.formula.into())
    }
}

impl<T: Term> Formula for Literal<T> {
    type Term = T;

    fn signature(&self) -> Result<Sig, Error> {
        match self {
            Literal::Pos(this) => this.signature(),
            Literal::Neg(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match self {
            Literal::Pos(this) => this.free_vars(),
            Literal::Neg(this) => this.free_vars(),
        }
    }

    fn transform(&self, f: &impl Fn(&T) -> T) -> Self {
        match self {
            Literal::Pos(this) => this.transform(f).into(),
            Literal::Neg(this) => this.transform(f).into(),
        }
    }
}

/// Represents a collection of [`Literal`]s.
///
/// **Note:**
/// The interpretation of a clause depends on its syntactic context.
/// For example, a [`CNF`] clause is interpreted as disjunction of literals whereas
/// a [`DNF`] clause corresponds to a conjunction of literals.
///
/// [`CNF`]: crate::transform::CNF
/// [`DNF`]: crate::transform::DNF
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct Clause<T: Term>(BTreeSet<Literal<T>>);

impl<T: Term> Clause<T> {
    /// Returns the literals of the receiver clause.
    pub fn literals(&self) -> &BTreeSet<Literal<T>> {
        &self.0
    }

    /// Consumes the receiver and returns its underlying list of [`Literal`]s.
    pub fn into_literals(self) -> BTreeSet<Literal<T>> {
        self.0
    }
}

impl<T: Term + Ord + Clone> Clause<T> {
    /// Returns a clause containing all literals in the receiver and `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().into()
    }
}

impl<T: Term> Deref for Clause<T> {
    type Target = BTreeSet<Literal<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Term + Ord> From<Literal<T>> for Clause<T> {
    fn from(value: Literal<T>) -> Self {
        vec![value].into_iter().into()
    }
}

impl<T, I> From<I> for Clause<T>
where
    T: Term + Ord,
    I: IntoIterator<Item = Literal<T>>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl<T: Term + Ord> Default for Clause<T> {
    fn default() -> Self {
        Self(BTreeSet::<_>::new())
    }
}

impl<T: Term + Ord> Formula for Clause<T> {
    type Term = T;

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

    fn transform(&self, f: &impl Fn(&T) -> T) -> Self {
        self.0.iter().map(|lit| lit.transform(f)).into()
    }
}

/// Represents a (multi-)set of [`Clause`]s.
///
/// **Note:**
/// The interpretation of a clause set depends on its syntactic context. For example,
/// a [`CNF`] is a clause set that is interpreted as a conjunction of clauses where each
/// clause is a disjunction of literals. In contrast, a [`DNF`] is a clause set that
/// corresponds to a disjunction of clauses where each clause is a conjunction of literals.
///
/// [`CNF`]: crate::transform::CNF
/// [`DNF`]: crate::transform::DNF
#[derive(Clone, Debug)]
pub struct ClauseSet<T: Term>(BTreeSet<Clause<T>>);

impl<T: Term + Ord> From<Clause<T>> for ClauseSet<T> {
    fn from(value: Clause<T>) -> Self {
        vec![value].into_iter().into()
    }
}

impl<T, I> From<I> for ClauseSet<T>
where
    T: Term + Ord,
    I: IntoIterator<Item = Clause<T>>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl<T: Term> ClauseSet<T> {
    /// Returns the clauses of the receiver.
    pub fn clauses(&self) -> &BTreeSet<Clause<T>> {
        &self.0
    }

    /// Consumes the receiver and returns its underlying clauses.
    pub fn into_clauses(self) -> BTreeSet<Clause<T>> {
        self.0
    }
}

impl<T: Term + Ord + Clone> ClauseSet<T> {
    /// Returns a clause set, containing all clauses in the receiver and `other`.    
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().into()
    }

    /// Returns a new clause set obtained by removing duplicate clauses of the reciever.
    /// It also removes duplicate (positive) literals in each clause.
    pub fn simplify(&self) -> Self {
        self.iter()
            .filter(|c1| !self.iter().any(|c2| *c1 != c2 && c2.is_subset(c1)))
            .cloned()
            .collect_vec()
            .into()
    }
}

impl<T: Term> Deref for ClauseSet<T> {
    type Target = BTreeSet<Clause<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Term + Ord> Default for ClauseSet<T> {
    fn default() -> Self {
        BTreeSet::<Clause<T>>::new().into()
    }
}

impl<T: Term + Ord> Formula for ClauseSet<T> {
    type Term = T;

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

    fn transform(&self, f: &impl Fn(&T) -> T) -> Self {
        self.0.iter().map(|clause| clause.transform(f)).into()
    }
}

/// Represents a collection of [`Atomic`]s as positive literals.
///
/// **Note:**
/// The interpretation of a positive clause depends on its syntactic context.
/// For example, a positive clause is the body or the head of a [`GNF`] corresponds to
/// a conjunction of positive literals.
///
/// [`GNF`]: crate::transform::GNF
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct PosClause<T: Term>(BTreeSet<Atomic<T>>);

impl<T> PosClause<T>
where
    T: Term,
{
    /// Returns the atomic formulae of the receiver clause.
    pub fn atomics(&self) -> &BTreeSet<Atomic<T>> {
        &self.0
    }

    /// Consumes the receiver and returns its underlying list of [`Atomic`]s.
    pub fn into_atomics(self) -> BTreeSet<Atomic<T>> {
        self.0
    }
}

impl<T> PosClause<T>
where
    T: Term + Ord + Clone,
{
    /// Returns a new clause, resulting from the joinging the atomic formulae of the
    /// receiver and `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().into()
    }
}

impl<T: Term> Deref for PosClause<T> {
    type Target = BTreeSet<Atomic<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Term + Ord> From<Atomic<T>> for PosClause<T> {
    fn from(value: Atomic<T>) -> Self {
        vec![value].into_iter().into()
    }
}

impl<T: Term + Ord> From<Atom<T>> for PosClause<T> {
    fn from(value: Atom<T>) -> Self {
        let atomic = Atomic::from(value);
        vec![atomic].into_iter().into()
    }
}

impl<T: Term + Ord> From<Equals<T>> for PosClause<T> {
    fn from(value: Equals<T>) -> Self {
        let atomic = Atomic::from(value);
        vec![atomic].into_iter().into()
    }
}

impl<T, I> From<I> for PosClause<T>
where
    T: Term + Ord,
    I: IntoIterator<Item = Atomic<T>>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl<T: Term + Ord> Default for PosClause<T> {
    fn default() -> Self {
        Vec::<Atomic<_>>::new().into()
    }
}

impl<T: Term + Ord> Formula for PosClause<T> {
    type Term = T;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&V> {
        self.iter().flat_map(|lit| lit.free_vars()).collect()
    }

    fn transform(&self, f: &impl Fn(&T) -> T) -> Self {
        self.iter().map(|lit| lit.transform(f)).into()
    }
}

/// Represents a (multi-)set of [`PosClause`]s.
///
/// **Note:**
/// The interpretation of a positive clause set depends on its syntactic context.
/// For example, a positive clause set is the head of a [`GNF`] is interpreted as disjunction
/// of [`PosClause`]s where each clause is a conjunction of positive literals.
///
/// [`GNF`]: crate::transform::GNF
#[derive(Clone, Debug)]
pub struct PosClauseSet<T: Term>(BTreeSet<PosClause<T>>);

impl<T> PosClauseSet<T>
where
    T: Term,
{
    /// Returns the clauses of the receiver.
    pub fn clauses(&self) -> &BTreeSet<PosClause<T>> {
        &self.0
    }

    /// Consumes the receiver and returns its underlying clauses.
    pub fn into_clauses(self) -> BTreeSet<PosClause<T>> {
        self.0
    }
}

impl<T> PosClauseSet<T>
where
    T: Term + Clone + Ord,
{
    /// Returns a new positive clause set, containing clauses obtained by pairwise unioning
    /// of the clauses in the receiver and `other`.
    pub fn cross_union(&self, other: &Self) -> Self {
        self.iter()
            .flat_map(|h1| other.iter().map(move |h2| h1.union(&h2)))
            .into()
    }

    /// Returns a new clause set obtained by removing duplicate clauses of the reciever.
    /// It also removes duplicate (positive) literals in each clause.
    pub fn simplify(&self) -> Self {
        self.iter()
            .filter(|c1| !self.iter().any(|c2| *c1 != c2 && c2.is_subset(c1)))
            .cloned()
            .collect_vec()
            .into()
    }
}

impl<T: Term + Ord> From<PosClause<T>> for PosClauseSet<T> {
    fn from(value: PosClause<T>) -> Self {
        vec![value].into_iter().into()
    }
}

impl<T, I> From<I> for PosClauseSet<T>
where
    T: Term + Ord,
    I: IntoIterator<Item = PosClause<T>>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl<T: Term> Deref for PosClauseSet<T> {
    type Target = BTreeSet<PosClause<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Term + Ord> Default for PosClauseSet<T> {
    fn default() -> Self {
        Vec::<PosClause<T>>::new().into()
    }
}

impl<T: Term + Ord> Formula for PosClauseSet<T> {
    type Term = T;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&V> {
        self.iter()
            .flat_map(|lit| lit.free_vars())
            .unique()
            .collect()
    }

    fn transform(&self, f: &impl Fn(&T) -> T) -> Self {
        self.iter().map(|lit| lit.transform(f)).into()
    }
}
