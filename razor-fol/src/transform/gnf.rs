/*! Defines formulae in Geometric Normal Form (GNF) and implements an algorithm for
converting [`CNF`] to [`GNF`].

[`CNF`]: crate::transform::CNF
*/
use super::{CNF_Clause, TermBased, CNF};
use crate::syntax::{formula::*, Error, Sig, Term, FOF, V};
use itertools::Itertools;
use std::ops::Deref;

/// Is the body of a formula in geometric form, representing the conjunctino of a list of
/// [`Atomic`] formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Body(Vec<Atomic>);

impl From<Atomic> for Body {
    fn from(value: Atomic) -> Self {
        Self(vec![value])
    }
}

impl<I: IntoIterator<Item = Atomic>> From<I> for Body {
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Default for Body {
    fn default() -> Self {
        Self::from(Vec::<Atomic>::new())
    }
}

impl Deref for Body {
    type Target = [Atomic];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl TermBased for Body {
    fn free_vars(&self) -> Vec<&V> {
        self.iter()
            .flat_map(|lit| lit.free_vars())
            .unique()
            .collect()
    }

    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self(self.0.iter().map(|lit| lit.transform(f)).collect())
    }
}

impl Formula for Body {
    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|a| a.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }
}

impl From<Body> for FOF {
    fn from(value: Body) -> Self {
        value
            .0
            .into_iter()
            .map(|atom| match atom {
                Atomic::Atom(this) => FOF::from(this),
                Atomic::Equals(this) => this.into(),
            })
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

/// Is a branch in the head of a formula in geometric form, representing the conjunctino of
/// a list of [`Atomic`] formulae.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Head(Vec<Atomic>);

impl Head {
    /// Returns a new [`Head`], resulting from the conjunction of the receiver and `other`.
    pub fn and(&self, other: &Self) -> Self {
        self.iter().chain(other.iter()).cloned().into()
    }

    /// Returns true if the receiver shadows the `other` clause; that is, if `other` is true,
    /// then the receiver clause has to be true as well.
    fn shadows(&self, other: &Self) -> bool {
        (self.len() < other.len() || (self.len() == other.len() && self != other))
            && self.iter().all(|cc| other.iter().any(|c| cc == c))
    }
}

impl From<Atomic> for Head {
    fn from(value: Atomic) -> Self {
        Self(vec![value])
    }
}

impl<I: IntoIterator<Item = Atomic>> From<I> for Head {
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Default for Head {
    fn default() -> Self {
        Self::from(Vec::<Atomic>::new())
    }
}

impl Deref for Head {
    type Target = [Atomic];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl TermBased for Head {
    fn free_vars(&self) -> Vec<&V> {
        self.iter().flat_map(|lit| lit.free_vars()).collect()
    }

    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self(self.iter().map(|lit| lit.transform(f)).collect())
    }
}

impl Formula for Head {
    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }
}

impl From<Head> for FOF {
    fn from(value: Head) -> Self {
        value
            .0
            .into_iter()
            .map(|atom| match atom {
                Atomic::Atom(this) => FOF::from(this),
                Atomic::Equals(this) => this.into(),
            })
            .fold1(|item, acc| item.and(acc))
            .unwrap_or(FOF::Top)
    }
}

/// Represents the disjunction of [`Head`]s in the head of a formula in geometric form.
#[derive(Clone, Debug)]
pub struct Heads(Vec<Head>);

impl Heads {
    /// Returns a simplified DNF equivalent to the receiver.
    pub fn simplify(&self) -> Self {
        let clauses = self
            .iter()
            .map(|c| Head::from(c.iter().unique().cloned()))
            .collect_vec();

        clauses
            .iter()
            .filter(|c1| !clauses.iter().any(|c2| c2.shadows(c1)))
            .cloned()
            .unique()
            .collect_vec()
            .into()
    }

    /// Returns a new instance of [`Heads`], corresponding to the conjunction of the
    /// receiver and `other` after syntanctic transformation.
    pub fn and(&self, other: &Self) -> Self {
        self.iter()
            .flat_map(|h1| other.iter().map(move |h2| h1.and(h2)))
            .into()
    }
}

impl From<Head> for Heads {
    fn from(value: Head) -> Self {
        Self(vec![value])
    }
}

impl<I: IntoIterator<Item = Head>> From<I> for Heads {
    fn from(value: I) -> Self {
        Self(value.into_iter().collect())
    }
}

impl Deref for Heads {
    type Target = [Head];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Default for Heads {
    fn default() -> Self {
        Self::from(Vec::<Head>::new())
    }
}

impl TermBased for Heads {
    fn free_vars(&self) -> Vec<&V> {
        self.iter()
            .flat_map(|lit| lit.free_vars())
            .unique()
            .collect()
    }

    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self(self.iter().map(|lit| lit.transform(f)).collect())
    }
}

impl Formula for Heads {
    fn signature(&self) -> Result<Sig, Error> {
        Sig::new_from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }
}

impl From<Heads> for FOF {
    fn from(value: Heads) -> Self {
        value
            .0
            .into_iter()
            .map(FOF::from)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
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
    body: Body,
    heads: Heads,
}

impl GNF {
    /// Returns the body of the receiver GNF.
    #[inline(always)]
    pub fn body(&self) -> &Body {
        &self.body
    }

    /// Returns the heads of the receiver GNF.
    #[inline(always)]
    pub fn heads(&self) -> &Heads {
        &self.heads
    }
}

impl From<(Body, Heads)> for GNF {
    fn from(value: (Body, Heads)) -> Self {
        let (body, heads) = value;
        Self { body, heads }
    }
}

impl TermBased for GNF {
    fn free_vars(&self) -> Vec<&V> {
        let mut b_vars = self.body.free_vars();
        b_vars.extend(self.heads.free_vars());
        b_vars
    }

    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        Self {
            body: self.body.transform(f),
            heads: self.heads.transform(f),
        }
    }
}

impl Formula for GNF {
    fn signature(&self) -> Result<Sig, Error> {
        let sig = self.body().signature()?;
        sig.merge(self.heads().signature()?)
    }
}

impl From<GNF> for FOF {
    fn from(value: GNF) -> Self {
        let body: FOF = value.body.into();
        body.implies(value.heads.into())
    }
}

// Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
fn gnf(clause: &CNF_Clause) -> GNF {
    let mut heads: Vec<Head> = Vec::new();
    let mut body: Vec<Atomic> = Vec::new();
    clause.iter().for_each(|lit| match lit {
        Literal::Pos(this) => heads.push(this.clone().into()),
        Literal::Neg(this) => body.push(this.clone()),
    });

    let body = Body::from(body);
    let heads = Heads::from(heads);
    (body, heads).into()
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
    ///     .map(|f| FOF::from(f).to_string())
    ///     .collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    pub fn gnf(&self) -> Vec<GNF> {
        self.iter().map(gnf).collect()
    }
}

#[cfg(test)]
mod test_transform {
    use super::*;
    use crate::{assert_debug_strings, syntax::Theory};

    fn gnf(formula: &FOF) -> Vec<FOF> {
        formula
            .pnf()
            .snf()
            .cnf()
            .gnf()
            .into_iter()
            .map(|gnf| gnf.into())
            .collect()
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
            assert_debug_strings!("true -> P('sk#0)", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(x) -> P(y) | Q(y)".parse().unwrap();
            assert_debug_strings!("(P(x) & Q(x)) -> (P(y) | Q(y))", gnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(x) -> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\n\
        P(x) -> Q(y)\n\
        Q(x) -> P(y)\n\
        Q(x) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "P(x) | Q(x) <=> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\n\
        P(x) -> Q(y)\n\
        Q(x) -> P(y)\n\
        Q(x) -> Q(y)\n\
        (P(y) & Q(y)) -> (P(x) | Q(x))",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (P(x) -> ?y. Q(x,y))".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x, sk#0(x))", gnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> (?y. (Q(y) & R(x, y)) | ?y. (P(y) & S(x, y)))))"
                .parse()
                .unwrap();
            assert_debug_strings!(
                "P(x) -> (Q(sk#0(x)) | P(sk#1(x)))\n\
        P(x) -> (Q(sk#0(x)) | S(x, sk#1(x)))\n\
        P(x) -> (R(x, sk#0(x)) | P(sk#1(x)))\n\
        P(x) -> (R(x, sk#0(x)) | S(x, sk#1(x)))",
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
            assert_debug_strings!(
                "((P(x) & Q(y)) & R(x, y)) -> S(x, y)\n\
        ((P(x) & Q(y)) & S(x, y)) -> R(x, y)\n\
        true -> ((R(x, y) | S(x, y)) | P(x))\n\
        true -> ((R(x, y) | S(x, y)) | Q(y))\n\
        R(x, y) -> (R(x, y) | P(x))\n\
        R(x, y) -> (R(x, y) | Q(y))\n\
        S(x, y) -> (S(x, y) | P(x))\n\
        S(x, y) -> (S(x, y) | Q(y))\n\
        (S(x, y) & R(x, y)) -> P(x)\n\
        (S(x, y) & R(x, y)) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "? x. P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P('sk#0) -> Q('sk#0)", gnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x`) -> Q(x)", gnf(&formula));
        }
        {
            let formula: FOF = "? x. (P(x) -> Q(x))".parse().unwrap();
            assert_debug_strings!("P('sk#0) -> Q('sk#0)", gnf(&formula));
        }
        {
            let formula: FOF = "false -> P(x)".parse().unwrap();
            assert_debug_strings!("", gnf(&formula));
        }
    }

    #[test]
    fn test_gnf_theory() {
        // mostly testing if compression of heads works properly:
        {
            let theory: Theory<FOF> = "P('a); P('b);".parse().unwrap();
            assert_debug_strings!("true -> (P('a) & P('b))", theory.gnf().formulae());
        }
        {
            let theory: Theory<FOF> = "P('a); P(x);".parse().unwrap();
            assert_debug_strings!("true -> P(x)\ntrue -> P('a)", theory.gnf().formulae());
        }
        {
            let theory: Theory<FOF> = "P('a); P(x); P('b);".parse().unwrap();
            assert_debug_strings!(
                "true -> P(x)\ntrue -> (P(\'a) & P(\'b))",
                theory.gnf().formulae(),
            );
        }
        {
            let theory: Theory<FOF> = "(T() and V()) or (U() and V());".parse().unwrap();
            assert_debug_strings!(
                "true -> ((T() & V()) | (U() & V()))",
                theory.gnf().formulae()
            );
        }
    }
}
