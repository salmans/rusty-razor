/*! Defines formulae in Geometric Normal Form (GNF) and implements an algorithm for
converting [`CNF`] to [`GNF`].

[`CNF`]: crate::transform::CNF
*/
use super::{CNF, PNF, SNF};
use crate::syntax::{
    formula::{
        clause::{Clause, Literal, PosClause, PosClauseSet},
        *,
    },
    term::Complex,
    Error, Sig, FOF, V,
};
use itertools::Itertools;

// GNF positive clauses and clause sets are constructed over complex terms.
type GnfClause = PosClause<Complex>;
type GnfClauseSet = PosClauseSet<Complex>;

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
    body: GnfClause,

    /// Is the head of a GNF, consisting of a positive clause set.
    head: GnfClauseSet,
}

impl GNF {
    /// Returns the body of the receiver GNF.
    #[inline(always)]
    pub fn body(&self) -> &GnfClause {
        &self.body
    }

    /// Returns the head of the receiver GNF.
    #[inline(always)]
    pub fn head(&self) -> &GnfClauseSet {
        &self.head
    }

    // Renders each clause as conjunction of literals
    fn clause_to_fof(clause: GnfClause) -> FOF {
        clause
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

    // Renders each clause set as disjunction of clauses
    fn clause_set_to_fof(clause: GnfClauseSet) -> FOF {
        clause
            .into_clauses()
            .into_iter()
            .sorted()
            .into_iter()
            .map(Self::clause_to_fof)
            .fold1(|item, acc| item.or(acc))
            .unwrap_or(FOF::Bottom)
    }
}

impl From<(GnfClause, GnfClauseSet)> for GNF {
    fn from(value: (GnfClause, GnfClauseSet)) -> Self {
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

    fn free_vars(&self) -> Vec<&V> {
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
        let body = GNF::clause_to_fof(value.body);
        let head = GNF::clause_set_to_fof(value.head);
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
    let mut head: Vec<PosClause<_>> = Vec::new();
    let mut body: Vec<Atomic<_>> = Vec::new();
    clause.iter().for_each(|lit| match lit {
        Literal::Pos(this) => head.push(this.clone().into()),
        Literal::Neg(this) => body.push(this.clone()),
    });

    let body = PosClause::from(body);
    let head = PosClauseSet::from(head);
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
        self.iter().map(gnf).collect()
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
        self.snf().cnf().gnf()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_debug_strings, syntax::Theory};
    use itertools::Itertools;

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
                "P(x) -> P(y)\nQ(x) -> P(y)\nP(x) -> Q(y)\nQ(x) -> Q(y)",
                gnf(&formula),
            );
        }
        {
            let formula: FOF = "P(x) | Q(x) <=> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "(P(y) & Q(y)) -> (P(x) | Q(x))\nP(x) -> P(y)\nQ(x) -> P(y)\nP(x) -> Q(y)\nQ(x) -> Q(y)",
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
"P(x) -> (P(sk#1(x)) | Q(sk#0(x)))\nP(x) -> (P(sk#1(x)) | R(x, sk#0(x)))\nP(x) -> (Q(sk#0(x)) | S(x, sk#1(x)))\nP(x) -> (R(x, sk#0(x)) | S(x, sk#1(x)))",                
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
            assert_debug_strings!("true -> ((P(x) | R(x, y)) | S(x, y))\nR(x, y) -> (P(x) | R(x, y))\nS(x, y) -> (P(x) | S(x, y))\n(R(x, y) & S(x, y)) -> P(x)\ntrue -> ((Q(y) | R(x, y)) | S(x, y))\nR(x, y) -> (Q(y) | R(x, y))\nS(x, y) -> (Q(y) | S(x, y))\n(R(x, y) & S(x, y)) -> Q(y)\n((P(x) & Q(y)) & S(x, y)) -> R(x, y)\n((P(x) & Q(y)) & R(x, y)) -> S(x, y)",
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
        // mostly testing if compression of head works properly:
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
