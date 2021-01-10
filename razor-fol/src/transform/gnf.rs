/*! Defines formulae in Geometric Normal Form (GNF) and implements an algorithm for
converting [`CNF`] to [`GNF`].

[`CNF`]: crate::transform::CNF
*/
use super::{CNF, PNF, SNF};
use crate::syntax::{
    formula::{
        clause::{Clause, Literal},
        *,
    },
    term::Complex,
    Error, Sig, Theory, Var, FOF,
};
use itertools::Itertools;
use std::{collections::BTreeSet, ops::Deref};

// A positive literal is simply an atomic formula.
type PosLiteral = Atomic<Complex>;

/// A Positive Conjunctive Formula (PCF) represents a collection of [`Atomic`]s, interpreted
/// as a conjunction of positive literals. PCFs are building blocks of [`GNF`]s.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct PCF(BTreeSet<PosLiteral>);

impl PCF {
    /// Returns the atomic formulae of the receiver clause.
    pub fn atomics(&self) -> &BTreeSet<PosLiteral> {
        &self.0
    }

    /// Consumes the receiver and returns its underlying list of atomic formulae.
    pub fn into_atomics(self) -> BTreeSet<PosLiteral> {
        self.0
    }
}

impl PCF {
    /// Returns a new clause, resulting from the joinging the atomic formulae of the
    /// receiver and `other`.
    pub fn union(&self, other: &Self) -> Self {
        self.0.union(&other.0).cloned().into()
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
        vec![value].into_iter().into()
    }
}

impl From<Atom<Complex>> for PCF {
    fn from(value: Atom<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().into()
    }
}

impl From<Equals<Complex>> for PCF {
    fn from(value: Equals<Complex>) -> Self {
        let literal = Atomic::from(value);
        vec![literal].into_iter().into()
    }
}

impl<I> From<I> for PCF
where
    I: IntoIterator<Item = PosLiteral>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Default for PCF {
    fn default() -> Self {
        Vec::<PosLiteral>::new().into()
    }
}

impl Formula for PCF {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&Var> {
        self.iter().flat_map(|lit| lit.free_vars()).collect()
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        self.iter().map(|lit| lit.transform(f)).into()
    }
}

impl From<PCF> for FOF {
    fn from(value: PCF) -> Self {
        value
            .into_atomics()
            .into_iter()
            .sorted()
            .into_iter()
            .map(|atomic| match atomic {
                Atomic::Atom(this) => FOF::from(this),
                Atomic::Equals(this) => this.into(),
            })
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

impl From<&PCF> for FOF {
    fn from(value: &PCF) -> Self {
        value.clone().into()
    }
}

/// Represents a set of [`PCF`]s. A set of [`PCF`]s in the head of a [`GNF`] is
/// interpreted as disjunction of PCFs where PCF is a conjunction of positive literals.
#[derive(Clone, Debug)]
pub struct PcfSet(BTreeSet<PCF>);

impl PcfSet {
    /// Returns the clauses of the receiver.
    pub fn clauses(&self) -> &BTreeSet<PCF> {
        &self.0
    }

    /// Consumes the receiver and returns its underlying clauses.
    pub fn into_clauses(self) -> BTreeSet<PCF> {
        self.0
    }
}

impl PcfSet {
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

impl From<PCF> for PcfSet {
    fn from(value: PCF) -> Self {
        vec![value].into_iter().into()
    }
}

impl<I> From<I> for PcfSet
where
    I: IntoIterator<Item = PCF>,
{
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Deref for PcfSet {
    type Target = BTreeSet<PCF>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Default for PcfSet {
    fn default() -> Self {
        Vec::<PCF>::new().into()
    }
}

impl Formula for PcfSet {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
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

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        self.iter().map(|lit| lit.transform(f)).into()
    }
}

impl From<PcfSet> for FOF {
    fn from(value: PcfSet) -> Self {
        value
            .into_clauses()
            .into_iter()
            .sorted()
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
    }
}

impl From<&PcfSet> for FOF {
    fn from(value: &PcfSet) -> Self {
        value.clone().into()
    }
}

/// Is a wrapper around [`FOF`] that represents a formula in Geometric Normal Form (GNF).
///
/// **Hint**: For mor information about GNF, see [Geometric Logic in Computer Science][glics]
/// by Steve Vickers.
///
/// [glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
/// [`FOF`]: crate::syntax::FOF
#[derive(Clone, Debug)]
pub struct GNF {
    /// Is the body of a GNF, comprised of a positive clause.
    body: PCF,

    /// Is the head of a GNF, consisting of a positive clause set.
    head: PcfSet,
}

impl GNF {
    /// Returns the body of the receiver GNF.
    #[inline(always)]
    pub fn body(&self) -> &PCF {
        &self.body
    }

    /// Returns the head of the receiver GNF.
    #[inline(always)]
    pub fn head(&self) -> &PcfSet {
        &self.head
    }

    /// Consumes the receiver and returns its body and head.
    pub fn into_body_and_head(self) -> (PCF, PcfSet) {
        (self.body, self.head)
    }
}

impl From<(PCF, PcfSet)> for GNF {
    fn from(value: (PCF, PcfSet)) -> Self {
        let (body, head) = value;
        Self { body, head }
    }
}

impl Formula for GNF {
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

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        Self {
            body: self.body.transform(f),
            head: self.head.transform(f),
        }
    }
}

impl std::fmt::Display for GNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl From<GNF> for FOF {
    fn from(value: GNF) -> Self {
        let body = FOF::from(value.body);
        let head = FOF::from(value.head);
        body.implies(head)
    }
}

impl From<&GNF> for FOF {
    fn from(value: &GNF) -> Self {
        value.clone().into()
    }
}

// Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
fn gnf(clause: &Clause<Complex>) -> GNF {
    let mut head: Vec<PCF> = Vec::new();
    let mut body: Vec<Atomic<_>> = Vec::new();
    clause.iter().for_each(|lit| match lit {
        Literal::Pos(this) => head.push(this.clone().into()),
        Literal::Neg(this) => body.push(this.clone()),
    });

    let body = PCF::from(body);
    let head = PcfSet::from(head);
    (body, head).into()
}

impl CNF {
    /// Transforms the receiver CNF to a list of formulae in Geometric Normal Form (GNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "P(x) & (Q(x) | R(x))".parse().unwrap();
    /// let cnf = formula.pnf().snf().cnf();
    /// let gnfs = cnf.gnf();
    ///  
    /// let gnf_to_string: Vec<String> = gnfs
    ///     .into_iter()
    ///     .map(|f| f.to_string())
    ///     .collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    pub fn gnf(&self) -> Vec<GNF> {
        let gnfs = self.iter().map(gnf).collect();
        compress_geometric(gnfs)
    }
}

impl SNF {
    /// Transforms the receiver SNF to a list of formulae in Geometric Normal Form (GNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "P(x) & (Q(x) | R(x))".parse().unwrap();
    /// let snf = formula.pnf().snf();
    /// let gnfs = snf.gnf();
    ///  
    /// let gnf_to_string: Vec<String> = gnfs
    ///     .into_iter()
    ///     .map(|f| f.to_string())
    ///     .collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    pub fn gnf(&self) -> Vec<GNF> {
        self.cnf().gnf()
    }
}

impl PNF {
    /// Transforms the receiver PNF to a list of formulae in Geometric Normal Form (GNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "P(x) & (Q(x) | R(x))".parse().unwrap();
    /// let pnf = formula.pnf();
    /// let gnfs = pnf.gnf();
    ///  
    /// let gnf_to_string: Vec<String> = gnfs
    ///     .into_iter()
    ///     .map(|f| f.to_string())
    ///     .collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    pub fn gnf(&self) -> Vec<GNF> {
        self.snf().gnf()
    }
}

impl FOF {
    /// Transforms the receiver FOF to a list of formulae in Geometric Normal Form (GNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let fof: FOF = "P(x) & (Q(x) | R(x))".parse().unwrap();
    /// let gnfs = fof.gnf();
    ///  
    /// let gnf_to_string: Vec<String> = gnfs
    ///     .into_iter()
    ///     .map(|f| f.to_string())
    ///     .collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    pub fn gnf(&self) -> Vec<GNF> {
        self.pnf().gnf()
    }
}

impl Theory<FOF> {
    /// Transforms the given theory to a *geometric theory*, where all formulae are in
    /// Geometric Normal Form (GNF).
    ///
    /// **Hint**: For mor information about GNF, see [Geometric Logic in Computer Science][glics]
    /// by Steve Vickers.
    ///
    /// [glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{FOF, Theory};
    ///
    /// let theory: Theory<FOF> = r#"
    ///     not P(x) or Q(x);
    ///     Q(x) -> exists y. R(x, y);
    /// "#.parse().unwrap();
    /// assert_eq!(r#"P(x) → Q(x)
    /// Q(x) → R(x, f#0(x))"#, theory.gnf().to_string());
    /// ```
    pub fn gnf(&self) -> Theory<GNF> {
        use std::convert::TryFrom;

        let mut c_counter = 0;
        let mut f_counter = 0;
        let mut const_generator = || {
            let sk_name = format!("c#{}", c_counter);
            c_counter += 1;
            sk_name.into()
        };

        let mut fn_generator = || {
            let sk_name = format!("f#{}", f_counter);
            f_counter += 1;
            sk_name.into()
        };

        let formulae: Vec<GNF> = self
            .formulae()
            .iter()
            .flat_map(|f| {
                f.pnf()
                    .snf_with(&mut const_generator, &mut fn_generator)
                    .cnf()
                    .gnf()
            })
            .collect();

        // Assuming that the conversion does not change the signature of the theory, thus it's safe:
        Theory::try_from(compress_geometric(formulae)).unwrap()
    }
}

// a helper to merge sequents with syntactically identical bodies
fn compress_geometric(formulae: Vec<GNF>) -> Vec<GNF> {
    formulae
        .into_iter()
        .sorted_by(|first, second| first.body().cmp(second.body()))
        .into_iter()
        .coalesce(|first, second| {
            // merge the ones with the same body:
            let body_vars = first.body().free_vars();
            let head_vars = first.head().free_vars();
            // compress sequents with no free variables that show up only in head:
            if head_vars
                .iter()
                .all(|hv| body_vars.iter().any(|bv| bv == hv))
            {
                let body_vars = second.body().free_vars();
                let head_vars = second.head().free_vars();
                if head_vars
                    .iter()
                    .all(|hv| body_vars.iter().any(|bv| bv == hv))
                {
                    if first.body() == second.body() {
                        Ok(GNF::from((
                            first.body().clone(),
                            first.head().cross_union(second.head()),
                        )))
                    } else {
                        Err((first, second))
                    }
                } else {
                    Err((second, first))
                }
            } else {
                Err((first, second))
            }
        })
        .into_iter()
        .map(|g| (g.body().clone(), g.head().simplify()).into())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_debug_strings, syntax::Theory};
    use itertools::Itertools;

    fn gnf(formula: &FOF) -> Vec<FOF> {
        formula.gnf().into_iter().map(|gnf| gnf.into()).collect()
    }

    #[test]
    fn battery() {
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_strings!("true -> false", gnf(&formula));
        }
    }

    #[test]
    fn test_gnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_strings!("", gnf(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_strings!("true -> false", gnf(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)", gnf(&formula));
        }
        {
            let formula: FOF = "x = y".parse().unwrap();
            assert_debug_strings!("true -> (x = y)", gnf(&formula));
        }
        {
            let formula: FOF = "~P(x)".parse().unwrap();
            assert_debug_strings!("P(x) -> false", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x)", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)\ntrue -> Q(x)", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(x)".parse().unwrap();
            assert_debug_strings!("true -> (P(x) | Q(x))", gnf(&formula));
        }
        {
            let formula: FOF = "! x. P(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)", gnf(&formula));
        }
        {
            let formula: FOF = "? x. P(x)".parse().unwrap();
            assert_debug_strings!("true -> P('c#0)", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(x) -> P(y) | Q(y)".parse().unwrap();
            assert_debug_strings!("(P(x) & Q(x)) -> (P(y) | Q(y))", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(x) -> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\nP(x) -> Q(y)\nQ(x) -> P(y)\nQ(x) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "P(x) | Q(x) <=> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\nP(x) -> Q(y)\n(P(y) & Q(y)) -> (P(x) | Q(x))\nQ(x) -> P(y)\nQ(x) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> ?y. Q(x,y))".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x, f#0(x))", gnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> (?y. (Q(y) & R(x, y)) | ?y. (P(y) & S(x, y)))))"
                .parse()
                .unwrap();
            assert_debug_strings!(
                "P(x) -> ((P(f#1(x)) & S(x, f#1(x))) | (Q(f#0(x)) & R(x, f#0(x))))",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "!x, y. ((P(x) & Q(y)) -> (R(x, y) -> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings!("((P(x) & Q(y)) & R(x, y)) -> S(x, y)", gnf(&formula));
        }
        {
            let formula: FOF = "!x, y. ((P(x) & Q(y)) <=> (R(x, y) <=> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings!("true -> ((P(x) | R(x, y)) | S(x, y))\ntrue -> ((Q(y) | R(x, y)) | S(x, y))\n((P(x) & Q(y)) & R(x, y)) -> S(x, y)\n((P(x) & Q(y)) & S(x, y)) -> R(x, y)\nR(x, y) -> ((P(x) & Q(y)) | R(x, y))\n(R(x, y) & S(x, y)) -> (P(x) & Q(y))\nS(x, y) -> ((P(x) & Q(y)) | S(x, y))",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "? x. P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P('c#0) -> Q('c#0)", gnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x`) -> Q(x)", gnf(&formula));
        }
        {
            let formula: FOF = "? x. (P(x) -> Q(x))".parse().unwrap();
            assert_debug_strings!("P('c#0) -> Q('c#0)", gnf(&formula));
        }
        {
            let formula: FOF = "false -> P(x)".parse().unwrap();
            assert_debug_strings!("", gnf(&formula));
        }
    }

    #[test]
    fn test_gnf_theory() {
        // mostly testing if compression of head works properly:
        {
            let theory: Theory<FOF> = "P('a); P('b);".parse().unwrap();
            assert_eq!("⊤ → (P(\'a) ∧ P(\'b))", theory.gnf().to_string());
        }
        {
            let theory: Theory<FOF> = "P('a); P(x);".parse().unwrap();
            assert_eq!("⊤ → P(x)\n⊤ → P(\'a)", theory.gnf().to_string());
        }
        {
            let theory: Theory<FOF> = "P('a); P(x); P('b);".parse().unwrap();
            assert_eq!("⊤ → P(x)\n⊤ → (P(\'a) ∧ P(\'b))", theory.gnf().to_string(),);
        }
        {
            let theory: Theory<FOF> = "(T() and V()) or (U() and V());".parse().unwrap();
            assert_eq!("⊤ → ((T() ∧ V()) ∨ (U() ∧ V()))", theory.gnf().to_string());
        }
    }
}
