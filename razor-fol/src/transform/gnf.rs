/*! Implements conversion to Geometric Normal Form (GNF) for first-order formulae.*/

use super::CNF;
use crate::syntax::{symbol::Generator, FOF::*, *};
use itertools::Itertools;
use std::cmp::Ordering::Equal;

/// Is a wrapper around [`FOF`] that represents a formula in Geometric Normal Form (GNF).
///
/// **Hint**: For mor information about GNF, see [Geometric Logic in Computer Science][glics]
/// by Steve Vickers.
///
/// [glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
/// [`FOF`]: crate::syntax::FOF
#[derive(Clone, Debug)]
pub struct GNF(FOF);

impl GNF {
    /// Returns a reference to the first-order formula wrapped in the receiver NNF.
    #[inline(always)]
    pub fn formula(&self) -> &FOF {
        &self.0
    }
}

impl From<GNF> for FOF {
    fn from(gnf: GNF) -> Self {
        gnf.0
    }
}

// For any disjunct of the CNF, the negative literals form the body of the geometric form
// and the positive literals form its head:
fn split_sides(disjunct: FOF) -> (Vec<FOF>, Vec<FOF>) {
    match disjunct {
        Or(this) => {
            let (mut left_body, mut left_head) = split_sides(this.left);
            let (mut right_body, mut right_head) = split_sides(this.right);

            left_body.append(&mut right_body);
            let body: Vec<_> = left_body.into_iter().unique().collect();

            left_head.append(&mut right_head);
            let head: Vec<_> = left_head.into_iter().unique().collect();

            (body, head)
        }
        Not(this) => (vec![this.formula], vec![]),
        _ => (vec![], vec![disjunct]),
    }
}

// Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
fn to_implication(disjunct: FOF) -> GNF {
    let (body, head) = split_sides(disjunct);
    let body = body.into_iter().fold(Top, |x, y| x.and(y)).simplify();
    let head = head.into_iter().fold(Bottom, |x, y| x.or(y)).simplify();
    GNF(body.implies(head))
}

// Split the CNF to a set of disjuncts.
fn get_disjuncts(cnf: FOF) -> Vec<FOF> {
    match cnf {
        And(this) => {
            let mut left = get_disjuncts(this.left);
            let mut right = get_disjuncts(this.right);
            left.append(&mut right);
            left.into_iter().unique().collect()
        }
        _ => vec![cnf],
    }
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
        get_disjuncts(self.clone().into())
            .into_iter()
            .map(to_implication)
            .collect()
    }
}

// a helper to merge sequents with syntactically identical bodies
fn compress_geometric(formulae: Vec<GNF>) -> Vec<FOF> {
    let formulae: Vec<FOF> = formulae.into_iter().map(|gnf| gnf.into()).collect();
    formulae
        .into_iter()
        .sorted_by(|first, second| {
            // sort sequents by their body
            match (first, second) {
                (Implies(first), Implies(second)) => first.premise.cmp(&second.premise),
                _ => Equal,
            }
        })
        .into_iter()
        .coalesce(|first, second| {
            // merge the ones with the same body:
            match first {
                Implies(first) => {
                    let l_vars = first.premise.free_vars();
                    let r_vars = first.consequence.free_vars();
                    // compress sequents with no free variables that show up only in head:
                    if r_vars.iter().all(|rv| l_vars.iter().any(|lv| lv == rv)) {
                        match second {
                            Implies(second) => {
                                let l_vars = second.premise.free_vars();
                                let r_vars = second.consequence.free_vars();
                                if r_vars.iter().all(|rv| l_vars.iter().any(|lv| lv == rv)) {
                                    if first.premise == second.premise {
                                        Ok(second.premise.implies(
                                            first.consequence.clone().and(second.consequence),
                                        ))
                                    } else {
                                        Err(((*first).into(), (*second).into()))
                                    }
                                } else {
                                    Err(((*second).into(), (*first).into()))
                                }
                            }
                            _ => Err((second, (*first).into())),
                        }
                    } else {
                        Err(((*first).into(), second))
                    }
                }
                _ => Err((first, second)),
            }
        })
        .map(|f| {
            // convert the head to dnf and simplify it:
            match f {
                Implies(this) => this
                    .premise
                    .implies(simplify_dnf(this.consequence.pnf().snf().dnf().into())),
                _ => f,
            }
        })
        .collect()
}

// Simplifies the given DNF as a helper for compress geometric.
fn simplify_dnf(formula: FOF) -> FOF {
    fn disjunct_list(formula: FOF) -> Vec<FOF> {
        match formula {
            Or(this) => {
                let mut lefts = disjunct_list(this.left);
                let mut rights = disjunct_list(this.right);
                lefts.append(&mut rights);
                lefts
            }
            _ => vec![formula],
        }
    }

    fn conjunct_list(formula: FOF) -> Vec<FOF> {
        match formula {
            And(this) => {
                let mut lefts = conjunct_list(this.left);
                let mut rights = conjunct_list(this.right);
                lefts.append(&mut rights);
                lefts
            }
            _ => vec![formula],
        }
    }

    let disjuncts: Vec<Vec<_>> = disjunct_list(formula)
        .into_iter()
        .map(|d| conjunct_list(d).into_iter().unique().collect())
        .collect();

    let disjuncts: Vec<Vec<_>> = disjuncts
        .iter()
        .filter(|d| {
            !disjuncts.iter().any(|dd| {
                (dd.len() < d.len() || (dd.len() == d.len() && dd < d))
                    && dd.iter().all(|cc| d.iter().any(|c| cc == c))
            })
        })
        .cloned()
        .unique()
        .collect();

    disjuncts
        .into_iter()
        .map(|d| d.into_iter().fold1(|f1, f2| f1.and(f2)).unwrap())
        .fold1(|f1, f2| f1.or(f2))
        .unwrap()
}

impl Theory {
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
    /// # use razor_fol::syntax::Theory;
    ///
    /// let theory: Theory = r#"
    ///     not P(x) or Q(x);
    ///     Q(x) -> exists y. R(x, y);
    /// "#.parse().unwrap();
    /// assert_eq!(r#"P(x) → Q(x)
    /// Q(x) → R(x, sk#0(x))"#, theory.gnf().to_string());
    /// ```
    pub fn gnf(&self) -> Theory {
        use core::convert::TryFrom;

        let mut generator = Generator::new().set_prefix("sk#");
        let formulae: Vec<GNF> = self
            .formulae()
            .iter()
            .flat_map(|f| f.pnf().snf_with(&mut generator).cnf().gnf())
            .collect();

        // assuming that conversion to gnf won't change the signature
        Theory::try_from(compress_geometric(formulae)).unwrap()
    }
}

#[cfg(test)]
mod test_transform {
    use super::*;
    use crate::assert_debug_strings;

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
    fn test_gnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_strings!("true -> true", gnf(&formula));
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
            assert_debug_strings!("true -> true", gnf(&formula));
        }
    }

    #[test]
    fn test_gnf_theory() {
        // mostly testing if compression of heads works properly:
        {
            let theory: Theory = "P('a); P('b);".parse().unwrap();
            assert_debug_strings!("true -> (P('a) & P('b))", theory.gnf().formulae());
        }
        {
            let theory: Theory = "P('a); P(x);".parse().unwrap();
            assert_debug_strings!("true -> P(x)\ntrue -> P('a)", theory.gnf().formulae());
        }
        {
            let theory: Theory = "P('a); P(x); P('b);".parse().unwrap();
            assert_debug_strings!(
                "true -> P(x)\ntrue -> (P(\'a) & P(\'b))",
                theory.gnf().formulae(),
            );
        }
        {
            let theory: Theory = "(T() and V()) or (U() and V());".parse().unwrap();
            assert_debug_strings!(
                "true -> ((T() & V()) | (U() & V()))",
                theory.gnf().formulae()
            );
        }
    }
}
