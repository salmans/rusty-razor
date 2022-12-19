/*! Defines formulae in Geometric Normal Form (GNF) and implements an algorithm for
transforming a [`CnfClauseSet`] to a [`Gnf`].

[`CnfClauseSet`]: crate::transform::CnfClauseSet
*/
use super::{Snf, ToSnf};
use crate::syntax::{
    formula::{
        clause::{Clause, Literal},
        *,
    },
    term::Complex,
    Error, Fof, Pred, Sig, Var,
};
use itertools::Itertools;
use std::{collections::BTreeSet, convert::TryFrom, iter::FromIterator, ops::Deref};

// A positive literal is simply an atomic formula.
type PosLiteral = Atomic<Complex>;

/// A Positive Conjunctive Formula (PCF) represents a collection of [`Atomic`]s, interpreted
/// as a conjunction of positive literals. PCFs are the building blocks of [`Gnf`]s.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Debug)]
pub struct Pcf(BTreeSet<PosLiteral>);

impl Pcf {
    /// Returns the positive literals of `self`.
    #[inline(always)]
    pub fn literals(&self) -> &BTreeSet<PosLiteral> {
        &self.0
    }

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

impl Deref for Pcf {
    type Target = BTreeSet<PosLiteral>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<PosLiteral> for Pcf {
    fn from(value: PosLiteral) -> Self {
        vec![value].into_iter().collect()
    }
}

impl From<Atom<Complex>> for Pcf {
    fn from(value: Atom<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().collect()
    }
}

impl From<Equals<Complex>> for Pcf {
    fn from(value: Equals<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().collect()
    }
}

impl FromIterator<PosLiteral> for Pcf {
    fn from_iter<T: IntoIterator<Item = PosLiteral>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for Pcf {
    type Item = PosLiteral;

    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl From<Vec<PosLiteral>> for Pcf {
    fn from(value: Vec<PosLiteral>) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Formula for Pcf {
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

impl From<Pcf> for Fof {
    fn from(value: Pcf) -> Self {
        value
            .into_literals()
            .into_iter()
            .sorted()
            .into_iter()
            .map(|atomic| match atomic {
                Atomic::Atom(this) => Fof::from(this),
                Atomic::Equals(this) => this.into(),
            })
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(Fof::Top)
    }
}

impl From<&Pcf> for Fof {
    fn from(value: &Pcf) -> Self {
        value.clone().into()
    }
}

impl TryFrom<Fof> for Pcf {
    type Error = super::Error;

    fn try_from(value: Fof) -> Result<Self, Self::Error> {
        match value {
            Fof::Top => Ok(Self::default()),
            Fof::Atom(atom) => Ok(Self::from(atom)),
            Fof::Equals(equals) => Ok(Self::from(equals)),
            Fof::And(and) => {
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

/// An Existential Positive Conjunctive Formula (EPCF) is a [`Pcf`],
/// possibly with existentially quantified variables.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Debug)]
pub struct Epcf {
    variables: Vec<Var>,
    pcf: Pcf,
}

impl Epcf {
    /// Returns the existentially quantified variables of `self`.
    #[inline(always)]
    pub fn variables(&self) -> &[Var] {
        &self.variables
    }

    /// Returns the PCF of `self`.
    #[inline(always)]
    pub fn pcf(&self) -> &Pcf {
        &self.pcf
    }
}

impl From<Pcf> for Epcf {
    fn from(pcf: Pcf) -> Self {
        Self {
            variables: Vec::new(),
            pcf,
        }
    }
}

impl<T> From<T> for Epcf
where
    T: Into<PosLiteral>,
{
    fn from(value: T) -> Self {
        let value: PosLiteral = value.into();
        Pcf::from(value).into()
    }
}

impl From<Vec<PosLiteral>> for Epcf {
    fn from(value: Vec<PosLiteral>) -> Self {
        Pcf::from(value).into()
    }
}

impl From<Epcf> for Fof {
    fn from(epcf: Epcf) -> Self {
        if epcf.variables().is_empty() {
            epcf.pcf().into()
        } else {
            Self::exists(epcf.variables, epcf.pcf.into())
        }
    }
}

impl From<&Epcf> for Fof {
    fn from(epcf: &Epcf) -> Self {
        epcf.clone().into()
    }
}

impl TryFrom<Fof> for Epcf {
    type Error = super::Error;

    fn try_from(value: Fof) -> Result<Self, Self::Error> {
        match value {
            Fof::Top | Fof::Atom(_) | Fof::Equals(_) | Fof::And(_) => {
                Pcf::try_from(value).map(Into::into)
            }
            Fof::Exists(exists) => {
                let inner = Epcf::try_from(exists.formula)?;
                let mut variables = exists.variables;
                variables.extend(inner.variables);
                Ok(Self {
                    variables,
                    pcf: inner.pcf,
                })
            }
            _ => Err(Self::Error::FofToGnf {
                formula: value.clone(),
            }),
        }
    }
}

impl Formula for Epcf {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        self.pcf().signature()
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.pcf().free_vars()
    }

    fn transform_term(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Self {
            variables: self.variables.clone(),
            pcf: self.pcf().transform_term(f),
        }
    }
}

/// Is a set of [`Epcf`]s in the head of a [`Gnf`], interpreted as a disjunction of
/// EPCFs where each EPCF is a conjunction of positive literals.
#[derive(PartialEq, Eq, Clone, Default, Debug)]
pub struct EpcfSet(BTreeSet<Epcf>);

impl EpcfSet {
    /// Returns the EPCFs of `self`.
    #[inline(always)]
    pub fn epcfs(&self) -> &BTreeSet<Epcf> {
        &self.0
    }

    /// Consumes `self` and returns its underlying set of EPCFs.
    pub fn into_epcfs(self) -> BTreeSet<Epcf> {
        self.0
    }

    // /// Returns a new EPCF set, containing the EPCFs obtained by pairwise unioning
    // /// of the EPCFs in `self` and `other`.
    // pub fn cross_union(&self, other: &Self) -> Self {
    //     self.iter()
    //         .flat_map(|h1| other.iter().map(move |h2| h1.union(h2)))
    //         .collect()
    // }

    // /// Returns a new EPCF set obtained by removing Epcfs that are
    // /// proper supersets of some other PCFs in `self`.
    // pub fn simplify(&self) -> Self {
    //     self.iter()
    //         .filter(|c1| !self.iter().any(|c2| *c1 != c2 && c2.is_subset(c1)))
    //         .cloned()
    //         .collect()
    // }
}

impl From<Epcf> for EpcfSet {
    fn from(value: Epcf) -> Self {
        vec![value].into_iter().collect()
    }
}

impl FromIterator<Epcf> for EpcfSet {
    fn from_iter<T: IntoIterator<Item = Epcf>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl IntoIterator for EpcfSet {
    type Item = Epcf;

    type IntoIter = std::collections::btree_set::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl From<Vec<Epcf>> for EpcfSet {
    fn from(value: Vec<Epcf>) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Deref for EpcfSet {
    type Target = BTreeSet<Epcf>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Formula for EpcfSet {
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

impl From<EpcfSet> for Fof {
    fn from(value: EpcfSet) -> Self {
        value
            .into_epcfs()
            .into_iter()
            .sorted()
            .into_iter()
            .map(Fof::from)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(Fof::Bottom)
    }
}

impl From<&EpcfSet> for Fof {
    fn from(value: &EpcfSet) -> Self {
        value.clone().into()
    }
}

/// Represents a formula in Geometric Normal Form (GNF), consisting of a [`Pcf`] in the body
/// (premise) and a [`PcfSet`] in the head (consequence).
///
/// **Hint**: For mor information about GNF, see [Geometric Logic in Computer Science][glics]
/// by Steve Vickers.
///
/// [glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
/// [`Fof`]: crate::syntax::Fof
#[derive(Clone, Debug)]
pub struct Gnf {
    /// Is the body of a GNF, comprised of a positive clause.
    body: Pcf,

    /// Is the head of a GNF, consisting of a positive clause set.
    head: EpcfSet,
}

impl Gnf {
    /// Returns the body of `self`.
    #[inline(always)]
    pub fn body(&self) -> &Pcf {
        &self.body
    }

    /// Returns the head of `self`.
    #[inline(always)]
    pub fn head(&self) -> &EpcfSet {
        &self.head
    }

    /// Consumes `self` and returns its body and head.
    pub fn into_body_and_head(self) -> (Pcf, EpcfSet) {
        (self.body, self.head)
    }
}

impl From<(Pcf, EpcfSet)> for Gnf {
    fn from(value: (Pcf, EpcfSet)) -> Self {
        let (body, head) = value;
        Self { body, head }
    }
}

impl TryFrom<Fof> for EpcfSet {
    type Error = super::Error;

    fn try_from(value: Fof) -> Result<Self, Self::Error> {
        match value {
            Fof::Top | Fof::Atom(_) | Fof::Equals(_) | Fof::And(_) => {
                Epcf::try_from(value).map(Self::from)
            }
            Fof::Bottom => Ok(Self::default()),
            Fof::Or(or) => {
                let mut result = Self::try_from(or.left)?.into_epcfs();
                result.extend(Self::try_from(or.right)?.into_epcfs());
                Ok(result.into_iter().collect())
            }
            _ => Err(Self::Error::FofToGnf {
                formula: value.clone(),
            }),
        }
    }
}

/// Is the trait of [`Formula`] types that can be transformed to a list of [`Gnf`]s.
pub trait ToGnf: Formula {
    /// Transforms `self` to a list of formulae in Geometric Normal
    /// Form (GNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Fof;
    /// use razor_fol::transform::ToGnf;
    ///
    /// let formula: Fof = "P(x) & (Q(x) | R(x))".parse().unwrap();
    /// let gnfs = formula.gnf();
    ///  
    /// let gnf_to_string: Vec<String> = gnfs
    ///     .into_iter()
    ///     .map(|f| f.to_string())
    ///     .collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    fn gnf(&self) -> Vec<Gnf>;
}

impl ToGnf for Snf {
    fn gnf(&self) -> Vec<Gnf> {
        use super::ToCnfClauseSet;

        let clauses = self.cnf_clause_set();
        clauses.iter().map(gnf).collect()
    }
}

impl<T: ToSnf> ToGnf for T {
    fn gnf(&self) -> Vec<Gnf> {
        self.snf().gnf()
    }
}

impl Formula for Gnf {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        let sig = self.body().signature()?;
        sig.merge(self.head().signature()?)
    }

    fn free_vars(&self) -> Vec<&Var> {
        let mut b_vars = self.body.free_vars();
        b_vars.extend(self.head.free_vars());
        b_vars.into_iter().unique().collect()
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            body: self.body.transform_term(f),
            head: self.head.transform_term(f),
        }
    }
}

impl std::fmt::Display for Gnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Fof::from(self).fmt(f)
    }
}

impl From<Gnf> for Fof {
    fn from(value: Gnf) -> Self {
        let body = Fof::from(value.body);
        let head = Fof::from(value.head);
        body.implies(head)
    }
}

impl From<&Gnf> for Fof {
    fn from(value: &Gnf) -> Self {
        value.clone().into()
    }
}

impl TryFrom<Fof> for Gnf {
    type Error = super::Error;

    fn try_from(value: Fof) -> Result<Self, Self::Error> {
        match value {
            Fof::Top => {
                let body = Pcf::default();
                let head = EpcfSet::from(Epcf::default());
                Ok((body, head).into())
            }
            Fof::Bottom => {
                let body = Pcf::default();
                let head = EpcfSet::default();
                Ok((body, head).into())
            }
            Fof::Atom(_) | Fof::Equals(_) | Fof::And(_) | Fof::Or(_) => {
                let head = EpcfSet::try_from(value)?;
                Ok((Pcf::default(), head).into())
            }
            Fof::Implies(implies) => {
                let body = Pcf::try_from(implies.premise)?;
                let head = EpcfSet::try_from(implies.consequence)?;
                Ok((body, head).into())
            }
            _ => Err(Self::Error::FofToGnf {
                formula: value.clone(),
            }),
        }
    }
}

// Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
fn gnf(clause: &Clause<Complex>) -> Gnf {
    let mut head: Vec<Epcf> = Vec::new();
    let mut body: Vec<Atomic<_>> = Vec::new();
    clause.iter().for_each(|lit| match lit {
        Literal::Pos(this) => head.push(Pcf::from(this.clone()).into()),
        Literal::Neg(this) => body.push(this.clone()),
    });

    let body = Pcf::from(body);
    let head = EpcfSet::from(head);
    (body, head).into()
}

use super::Dnf;
use std::collections::HashSet;

pub struct GnfFromDnfContext {
    pred_generator: Box<dyn FnMut() -> Pred>,
    neg_set: HashSet<Pred>,
}

impl GnfFromDnfContext {
    pub fn new<P>(pred_generator: P) -> Self
    where
        P: FnMut() -> Pred + 'static,
    {
        Self {
            pred_generator: Box::new(pred_generator),
            neg_set: HashSet::new(),
        }
    }
}

pub fn gnf_from_dnf(dnf: Dnf, context: &mut GnfFromDnfContext) -> Vec<Gnf> {
    gnf_from_dnf_helper(
        Pcf::default(),
        dnf,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        context,
    )
}

fn gnf_from_dnf_helper(
    body: Pcf,
    dnf: Dnf,
    mut univ_vars: Vec<Var>,
    exist_vars: Vec<Var>,
    mut theory: Vec<Gnf>,
    context: &mut GnfFromDnfContext,
) -> Vec<Gnf> {
    match dnf {
        Dnf::Clauses(c) => {
            let (thy, new_clauses) = dnf_clause_set(c, context);
            theory.extend(thy);
            let epcf_set = new_clauses
                .into_iter()
                .map(|c| Epcf {
                    variables: exist_vars
                        .iter()
                        .filter(|v| c.free_vars().contains(v))
                        .cloned()
                        .collect::<Vec<_>>()
                        .clone(),
                    pcf: c.into(),
                })
                .collect::<Vec<_>>();
            theory.push((body, EpcfSet::from(epcf_set)).into());
            theory
        }
        Dnf::Exists(exists) => {
            let pred = (context.pred_generator)();
            univ_vars.extend(exists.variables.clone());
            let atom: Atom<Complex> = pred.app(univ_vars.iter().map(Into::into).collect());
            let head_pcf: Pcf = atom.into();
            let head = Epcf {
                variables: exists.variables.clone(),
                pcf: head_pcf.clone(),
            };
            theory.push((body, EpcfSet::from(head)).into());
            gnf_from_dnf_helper(
                head_pcf,
                exists.formula,
                univ_vars,
                exists.variables,
                theory,
                context,
            )
        }
        Dnf::Forall(forall) => {
            univ_vars.extend(forall.variables);
            gnf_from_dnf_helper(body, forall.formula, univ_vars, Vec::new(), theory, context)
        }
    }
}

use crate::syntax::formula::clause::ClauseSet;
fn dnf_clause_set(
    clauses: ClauseSet<Complex>,
    context: &mut GnfFromDnfContext,
) -> (Vec<Gnf>, Vec<Vec<Atomic<Complex>>>) {
    let mut theory = Vec::<Gnf>::new();
    let mut new_clauses = Vec::new();

    for clause in clauses {
        let mut new_clause = Vec::new();
        for literal in clause {
            match literal {
                Literal::Pos(l) => new_clause.push(l),
                Literal::Neg(l) => match l {
                    Atomic::Atom(a) => {
                        let pred: Pred = format!("N#{}", a.predicate.to_string()).into();
                        if !context.neg_set.contains(&pred) {
                            let arity = a.terms.len();
                            let terms = (0..arity)
                                .into_iter()
                                .map(|i| Var::from(format!("x{}", i)).into())
                                .collect::<Vec<_>>();
                            theory.push(
                                (
                                    Pcf::from(vec![
                                        a.predicate.app(terms.clone()).into(),
                                        pred.clone().app(terms).into(),
                                    ]),
                                    EpcfSet::default(),
                                )
                                    .into(),
                            );
                            context.neg_set.insert(pred.clone());
                        }
                        new_clause.push(pred.app(a.terms).into());
                    }
                    Atomic::Equals(e) => {
                        let pred: Pred = "Neq#".into();
                        if !context.neg_set.contains(&pred) {
                            theory.push(
                                (
                                    Pcf::from(vec![
                                        pred.clone()
                                            .app(vec![
                                                Var::from("x1").into(),
                                                Var::from("x2").into(),
                                            ])
                                            .into(),
                                        Equals {
                                            left: Var::from("x1").into(),
                                            right: Var::from("x2").into(),
                                        }
                                        .into(),
                                    ]),
                                    EpcfSet::default(),
                                )
                                    .into(),
                            );
                            context.neg_set.insert(pred.clone());
                        }
                        new_clause.push(pred.app(vec![e.left, e.right]).into());
                    }
                },
            }
        }
        new_clauses.push(new_clause.into());
    }
    (theory, new_clauses)
}

use super::Cnf;
pub struct GnfFromCnfContext {
    pred_generator: Box<dyn FnMut() -> Pred>,
    trigger_generator: Box<dyn FnMut() -> Pred>,
}

impl GnfFromCnfContext {
    pub fn new<P, T>(pred_generator: P, trigger_generator: T) -> Self
    where
        P: FnMut() -> Pred + 'static,
        T: FnMut() -> Pred + 'static,
    {
        Self {
            pred_generator: Box::new(pred_generator),
            trigger_generator: Box::new(trigger_generator),
        }
    }
}

pub fn gnf_from_cnf(cnf: Cnf, context: &mut GnfFromCnfContext) -> Vec<Gnf> {
    gnf_from_cnf_helper(
        Pcf::default(),
        cnf,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        context,
    )
}

fn gnf_from_cnf_helper(
    body: Pcf,
    cnf: Cnf,
    mut univ_vars: Vec<Var>,
    exist_vars: Vec<Var>,
    mut theory: Vec<Gnf>,
    context: &mut GnfFromCnfContext,
) -> Vec<Gnf> {
    match cnf {
        Cnf::Clauses(c) => {
            let (thy, new_clause) = cnf_clause_set(c, context);
            theory.extend(thy);
            let epcf = Epcf {
                variables: exist_vars,
                pcf: new_clause.into(),
            };
            theory.push((body, EpcfSet::from(epcf)).into());
            theory
        }
        Cnf::Exists(exists) => {
            let pred = (context.pred_generator)();
            univ_vars.extend(exists.variables.clone());
            let atom: Atom<Complex> = pred.app(univ_vars.iter().map(Into::into).collect());
            let head_pcf: Pcf = atom.into();
            let head = Epcf {
                variables: exists.variables.clone(),
                pcf: head_pcf.clone(),
            };
            theory.push((body, EpcfSet::from(head)).into());
            gnf_from_cnf_helper(
                head_pcf,
                exists.formula,
                univ_vars,
                exists.variables,
                theory,
                context,
            )
        }
        Cnf::Forall(forall) => {
            univ_vars.extend(forall.variables);
            gnf_from_cnf_helper(body, forall.formula, univ_vars, Vec::new(), theory, context)
        }
    }
}

fn cnf_clause_set(
    clauses: ClauseSet<Complex>,
    context: &mut GnfFromCnfContext,
) -> (Vec<Gnf>, Vec<Atomic<Complex>>) {
    let mut theory = Vec::<Gnf>::new();
    let mut triggers = Vec::new();

    for clause in clauses {
        let trigger_pred = (context.trigger_generator)();
        let trigger: Atomic<Complex> = trigger_pred
            .app(clause.free_vars().into_iter().map(Into::into).collect())
            .into();
        triggers.push(trigger.clone());
        let mut body = vec![Atomic::from(trigger)];
        let mut head = Vec::new();

        for literal in clause {
            match literal {
                Literal::Pos(l) => head.push(Epcf::from(l)),
                Literal::Neg(l) => body.push(l),
            }
        }
        theory.push((Pcf::from(body), EpcfSet::from(head)).into());
    }
    (theory, triggers)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assert_debug_strings, assert_eq_sorted_vecs, fof,
        syntax::{
            signature::{FuncSig, PredSig},
            Sig, EQ_SYM,
        },
        term, v,
    };
    use itertools::Itertools;

    #[test]
    fn temp_test() {
        use super::super::ToDnf;
        {
            let formula: Fof = "P(x) | Q(x) -> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "",
                gnf_from_dnf(formula.dnf())
                    .into_iter()
                    .map(Fof::from)
                    .collect::<Vec<_>>()
            )
        }
    }

    fn gnf(formula: &Fof) -> Vec<Fof> {
        formula.gnf().into_iter().map(|gnf| gnf.into()).collect()
    }

    #[test]
    fn pcf_union() {
        {
            let first = Pcf::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            });
            let second = Pcf::default();
            assert_eq!(first, first.union(&second));
            assert_eq!(first, second.union(&first));
        }
        {
            let first = Pcf::from(Atom {
                predicate: "P".into(),
                terms: vec![],
            });
            let second = Pcf::from(vec![
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
            let expected = Pcf::from(vec![
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
            let pcf = Pcf::default();
            assert_eq!(Vec::<&Var>::new(), pcf.free_vars());
        }
        {
            let pcf = Pcf::from(vec![
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
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), pcf.free_vars());
        }
    }

    #[test]
    fn pcf_transform() {
        {
            let pcf: Pcf = Atomic::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(y)],
            })
            .into();
            let f = |t: &Complex| {
                {
                    if t == &term!(f(x)) {
                        term!(z)
                    } else {
                        t.clone()
                    }
                }
                .into()
            };
            assert_eq!(
                Pcf::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z), term!(y)],
                }),
                pcf.transform_term(&f)
            );
        }
        {
            let pcf: Pcf = Equals {
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
                Pcf::from(Equals {
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

            let pcf = Pcf::from(vec![
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
            let pcf = Pcf::from(vec![
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

    // #[test]
    // fn pcf_set_cross_union() {
    //     {
    //         let first = EpcfSet::default();
    //         let second = EpcfSet::default();
    //         assert_eq!(EpcfSet::default(), first.cross_union(&second));
    //     }
    //     {
    //         let first = EpcfSet::from(vec![Pcf::from(Atom {
    //             predicate: "P".into(),
    //             terms: vec![],
    //         })]);
    //         let second = EpcfSet::default();
    //         assert_eq!(EpcfSet::default(), first.cross_union(&second));
    //         assert_eq!(EpcfSet::default(), second.cross_union(&first));
    //     }
    //     {
    //         let first = EpcfSet::from(vec![Pcf::from(Atom {
    //             predicate: "P".into(),
    //             terms: vec![],
    //         })]);
    //         let second = EpcfSet::from(vec![Pcf::from(Atom {
    //             predicate: "P".into(),
    //             terms: vec![],
    //         })]);
    //         assert_eq!(first, first.cross_union(&second));
    //     }
    //     {
    //         let first = EpcfSet::from(vec![Pcf::from(Atom {
    //             predicate: "P".into(),
    //             terms: vec![],
    //         })]);
    //         let second = EpcfSet::from(vec![Pcf::from(Atom {
    //             predicate: "Q".into(),
    //             terms: vec![],
    //         })]);
    //         let expected = EpcfSet::from(vec![Pcf::from(vec![
    //             Atom {
    //                 predicate: "P".into(),
    //                 terms: vec![],
    //             }
    //             .into(),
    //             Atom {
    //                 predicate: "Q".into(),
    //                 terms: vec![],
    //             }
    //             .into(),
    //         ])]);
    //         assert_eq!(expected, first.cross_union(&second));
    //         assert_eq!(expected, second.cross_union(&first));
    //     }
    //     {
    //         let first = EpcfSet::from(vec![Pcf::from(Atom {
    //             predicate: "P".into(),
    //             terms: vec![],
    //         })]);
    //         let second = EpcfSet::from(vec![Pcf::from(vec![
    //             Atom {
    //                 predicate: "Q".into(),
    //                 terms: vec![],
    //             }
    //             .into(),
    //             Atom {
    //                 predicate: "R".into(),
    //                 terms: vec![],
    //             }
    //             .into(),
    //         ])]);
    //         let expected = EpcfSet::from(vec![Pcf::from(vec![
    //             Atom {
    //                 predicate: "P".into(),
    //                 terms: vec![],
    //             }
    //             .into(),
    //             Atom {
    //                 predicate: "Q".into(),
    //                 terms: vec![],
    //             }
    //             .into(),
    //             Atom {
    //                 predicate: "R".into(),
    //                 terms: vec![],
    //             }
    //             .into(),
    //         ])]);
    //         assert_eq!(expected, first.cross_union(&second));
    //         assert_eq!(expected, second.cross_union(&first));
    //     }
    //     {
    //         let first = EpcfSet::from(vec![
    //             Pcf::from(Atomic::from(Atom {
    //                 predicate: "P".into(),
    //                 terms: vec![],
    //             })),
    //             Pcf::from(Atomic::from(Atom {
    //                 predicate: "Q".into(),
    //                 terms: vec![],
    //             })),
    //         ]);
    //         let second = EpcfSet::from(vec![
    //             Pcf::from(Atomic::from(Atom {
    //                 predicate: "R".into(),
    //                 terms: vec![],
    //             })),
    //             Pcf::from(Atomic::from(Atom {
    //                 predicate: "S".into(),
    //                 terms: vec![],
    //             })),
    //         ]);
    //         let expected = EpcfSet::from(vec![
    //             Pcf::from(vec![
    //                 Atomic::from(Atom {
    //                     predicate: "P".into(),
    //                     terms: vec![],
    //                 }),
    //                 Atom {
    //                     predicate: "R".into(),
    //                     terms: vec![],
    //                 }
    //                 .into(),
    //             ]),
    //             Pcf::from(vec![
    //                 Atomic::from(Atom {
    //                     predicate: "P".into(),
    //                     terms: vec![],
    //                 }),
    //                 Atom {
    //                     predicate: "S".into(),
    //                     terms: vec![],
    //                 }
    //                 .into(),
    //             ]),
    //             Pcf::from(vec![
    //                 Atomic::from(Atom {
    //                     predicate: "Q".into(),
    //                     terms: vec![],
    //                 }),
    //                 Atom {
    //                     predicate: "R".into(),
    //                     terms: vec![],
    //                 }
    //                 .into(),
    //             ]),
    //             Pcf::from(vec![
    //                 Atomic::from(Atom {
    //                     predicate: "Q".into(),
    //                     terms: vec![],
    //                 }),
    //                 Atom {
    //                     predicate: "S".into(),
    //                     terms: vec![],
    //                 }
    //                 .into(),
    //             ]),
    //         ]);
    //         assert_eq!(expected, first.cross_union(&second));
    //         assert_eq!(expected, second.cross_union(&first));
    //     }
    // }

    // #[test]
    // fn pcf_set_simplify() {
    //     {
    //         let pcf_set = EpcfSet::default();
    //         assert_eq!(pcf_set, pcf_set.simplify());
    //     }
    //     {
    //         let pcf_set: EpcfSet = vec![Pcf::from(vec![Atomic::from(Atom {
    //             predicate: "P".into(),
    //             terms: vec![term!(x)],
    //         })])]
    //         .into();
    //         assert_eq!(pcf_set, pcf_set.simplify());
    //     }
    //     {
    //         let pcf_set: EpcfSet = vec![
    //             Pcf::from(vec![
    //                 Atomic::from(Atom {
    //                     predicate: "P".into(),
    //                     terms: vec![term!(x)],
    //                 }),
    //                 Atom {
    //                     predicate: "Q".into(),
    //                     terms: vec![term!(x)],
    //                 }
    //                 .into(),
    //             ]),
    //             Pcf::from(vec![Atomic::from(Atom {
    //                 predicate: "P".into(),
    //                 terms: vec![term!(x)],
    //             })]),
    //             Pcf::from(vec![Atomic::from(Atom {
    //                 predicate: "R".into(),
    //                 terms: vec![term!(x)],
    //             })]),
    //             Pcf::from(vec![Atomic::from(Atom {
    //                 predicate: "Q".into(),
    //                 terms: vec![term!(x)],
    //             })]),
    //         ]
    //         .into();
    //         let expected: EpcfSet = vec![
    //             Pcf::from(vec![Atomic::from(Atom {
    //                 predicate: "P".into(),
    //                 terms: vec![term!(x)],
    //             })]),
    //             Pcf::from(vec![Atomic::from(Atom {
    //                 predicate: "Q".into(),
    //                 terms: vec![term!(x)],
    //             })]),
    //             Pcf::from(vec![Atomic::from(Atom {
    //                 predicate: "R".into(),
    //                 terms: vec![term!(x)],
    //             })]),
    //         ]
    //         .into();
    //         assert_eq!(expected, pcf_set.simplify());
    //     }
    // }

    #[test]
    fn pcf_set_free_vars() {
        {
            let pcf_set = EpcfSet::default();
            assert_eq!(Vec::<&Var>::new(), pcf_set.free_vars());
        }
        {
            let pcf_set = EpcfSet::from(vec![
                Epcf::from(Atom {
                    predicate: "Q".into(),
                    terms: vec![term!(x)],
                }),
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
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), pcf_set.free_vars());
        }
    }

    #[test]
    fn pcf_set_transform() {
        {
            let pcf_set: EpcfSet = Epcf::from(Atom {
                predicate: "P".into(),
                terms: vec![term!(f(x)), term!(y)],
            })
            .into();
            let f = |t: &Complex| {
                {
                    if t == &term!(f(x)) {
                        term!(z)
                    } else {
                        t.clone()
                    }
                }
                .into()
            };
            assert_eq!(
                EpcfSet::from(Epcf::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(z), term!(y)],
                })),
                pcf_set.transform_term(&f)
            );
        }
        {
            let pcf_set: EpcfSet = Epcf::from(Equals {
                left: term!(f(x)),
                right: term!(y),
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
                EpcfSet::from(Epcf::from(Equals {
                    left: term!(z),
                    right: term!(y),
                })),
                pcf_set.transform_term(&f)
            );
        }
    }

    #[test]
    fn pcf_set_signature() {
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

            let pcf_set = EpcfSet::from(vec![
                Epcf::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }),
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
            assert_eq!(sig, pcf_set.signature().unwrap());
        }
        {
            let pcf_set = EpcfSet::from(vec![
                Epcf::from(Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x)],
                }),
                Atom {
                    predicate: "P".into(),
                    terms: vec![term!(x), term!(y)],
                }
                .into(),
            ]);
            assert!(pcf_set.signature().is_err());
        }
    }

    #[test]
    fn test_gnf() {
        {
            let formula: Fof = "true".parse().unwrap();
            assert_debug_strings!("", gnf(&formula));
        }
        {
            let formula: Fof = "false".parse().unwrap();
            assert_debug_strings!("true -> false", gnf(&formula));
        }
        {
            let formula: Fof = "P(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)", gnf(&formula));
        }
        {
            let formula: Fof = "x = y".parse().unwrap();
            assert_debug_strings!("true -> x = y", gnf(&formula));
        }
        {
            let formula: Fof = "~P(x)".parse().unwrap();
            assert_debug_strings!("P(x) -> false", gnf(&formula));
        }
        {
            let formula: Fof = "P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x)", gnf(&formula));
        }
        {
            let formula: Fof = "P(x) & Q(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)\ntrue -> Q(x)", gnf(&formula));
        }
        {
            let formula: Fof = "P(x) | Q(x)".parse().unwrap();
            assert_debug_strings!("true -> (P(x) | Q(x))", gnf(&formula));
        }
        {
            let formula: Fof = "! x. P(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)", gnf(&formula));
        }
        {
            let formula: Fof = "? x. P(x)".parse().unwrap();
            assert_debug_strings!("true -> P('c#0)", gnf(&formula));
        }
        {
            let formula: Fof = "P(x) & Q(x) -> P(y) | Q(y)".parse().unwrap();
            assert_debug_strings!("(P(x) & Q(x)) -> (P(y) | Q(y))", gnf(&formula));
        }
        {
            let formula: Fof = "P(x) | Q(x) -> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\nQ(x) -> P(y)\nP(x) -> Q(y)\nQ(x) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: Fof = "P(x) | Q(x) <=> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "(P(y) & Q(y)) -> (P(x) | Q(x))\nP(x) -> P(y)\nQ(x) -> P(y)\nP(x) -> Q(y)\nQ(x) -> Q(y)",             
                gnf(&formula),
            );
        }
        {
            let formula: Fof = "!x. (P(x) -> ?y. Q(x,y))".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x, f#0(x))", gnf(&formula));
        }
        {
            let formula: Fof = "!x. (P(x) -> (?y. (Q(y) & R(x, y)) | ?y. (P(y) & S(x, y))))"
                .parse()
                .unwrap();
            assert_debug_strings!(
                "P(x) -> (P(f#1(x)) | Q(f#0(x)))\nP(x) -> (P(f#1(x)) | R(x, f#0(x)))\nP(x) -> (Q(f#0(x)) | S(x, f#1(x)))\nP(x) -> (R(x, f#0(x)) | S(x, f#1(x)))",
                gnf(&formula),
            );
        }
        {
            let formula: Fof = "!x, y. ((P(x) & Q(y)) -> (R(x, y) -> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings!("((P(x) & Q(y)) & R(x, y)) -> S(x, y)", gnf(&formula));
        }
        {
            let formula: Fof = "!x, y. ((P(x) & Q(y)) <=> (R(x, y) <=> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings!("true -> ((P(x) | R(x, y)) | S(x, y))\nR(x, y) -> (P(x) | R(x, y))\nS(x, y) -> (P(x) | S(x, y))\n(R(x, y) & S(x, y)) -> P(x)\ntrue -> ((Q(y) | R(x, y)) | S(x, y))\nR(x, y) -> (Q(y) | R(x, y))\nS(x, y) -> (Q(y) | S(x, y))\n(R(x, y) & S(x, y)) -> Q(y)\n((P(x) & Q(y)) & S(x, y)) -> R(x, y)\n((P(x) & Q(y)) & R(x, y)) -> S(x, y)",
                gnf(&formula),
            );
        }
        {
            let formula: Fof = "? x. P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P('c#0) -> Q('c#0)", gnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x`) -> Q(x)", gnf(&formula));
        }
        {
            let formula: Fof = "? x. (P(x) -> Q(x))".parse().unwrap();
            assert_debug_strings!("P('c#0) -> Q('c#0)", gnf(&formula));
        }
        {
            let formula: Fof = "false -> P(x)".parse().unwrap();
            assert_debug_strings!("", gnf(&formula));
        }
    }

    #[test]
    fn gnf_free_vars() {
        {
            let gnf = fof!({'|'} -> {_|_}).gnf();
            assert_eq!(1, gnf.len());
            assert_eq!(Vec::<&Var>::new(), gnf[0].free_vars());
        }
        {
            let gnf = Gnf::try_from(fof!({[P(x, @c)] & [Q(y)]} -> {[Q(x)] | [ [Q(y)] & [R()] ]}))
                .unwrap();
            assert_eq_sorted_vecs!(vec![v!(x), v!(y)].iter().collect_vec(), gnf.free_vars());
        }
    }

    #[test]
    fn gnf_transform() {
        let gnf =
            Gnf::try_from(fof!({[P(y, f(x))] & [Q(x)]} -> {[Q(f(x))] | [[R(f(x))] & [R(y)]]}))
                .unwrap();
        let f = |t: &Complex| {
            {
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
            }
            .into()
        };
        assert_eq!(
            fof!({[P(y, z)] & [Q(x)]} -> {[Q(z)] | [[R(y)] & [R(z)]]}),
            Fof::from(gnf.transform_term(&f))
        );
    }

    #[test]
    fn gnf_signature() {
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

            let gnf = Gnf::try_from(
                fof!({[P(f(x, @c))] & [P(y)]} -> {[P(y)] | [[Q(x, x)] & [(x) = (y)]]}),
            )
            .unwrap();
            assert_eq!(sig, gnf.signature().unwrap());
        }
        {
            let gnf = Gnf::try_from(fof!({P(x, x)} -> {P(x)})).unwrap();
            assert!(gnf.signature().is_err());
        }
    }
}
