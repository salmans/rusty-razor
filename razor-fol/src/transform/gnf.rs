/*! Implements conversion to Geometric Normal Form (GNF) for formula.*/

use super::SkolemGenerator;
use crate::syntax::{Formula::*, *};
use itertools::Itertools;
use std::cmp::Ordering::Equal;

// For any disjunct of the CNF, the negative literals form the body of the geometric form
// and the positive literals form its head:
fn split_sides(disjunct: Formula) -> (Vec<Formula>, Vec<Formula>) {
    match disjunct {
        Or { left, right } => {
            let (mut left_body, mut left_head) = split_sides(*left);
            let (mut right_body, mut right_head) = split_sides(*right);

            left_body.append(&mut right_body);
            let body: Vec<Formula> = left_body.into_iter().unique().collect();

            left_head.append(&mut right_head);
            let head: Vec<Formula> = left_head.into_iter().unique().collect();

            (body, head)
        }
        Not { formula } => (vec![*formula], vec![]),
        _ => (vec![], vec![disjunct]),
    }
}

// Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
fn to_implication(disjunct: Formula) -> Formula {
    let (body, head) = split_sides(disjunct);
    let body = body.into_iter().fold(Top, |x, y| x.and(y)).simplify();
    let head = head.into_iter().fold(Bottom, |x, y| x.or(y)).simplify();
    body.implies(head)
}

// Split the CNF to a set of disjuncts.
fn get_disjuncts(cnf: Formula) -> Vec<Formula> {
    match cnf {
        And { left, right } => {
            let mut left = get_disjuncts(*left);
            let mut right = get_disjuncts(*right);
            left.append(&mut right);
            left.into_iter().unique().collect()
        }
        _ => vec![cnf],
    }
}

impl Formula {
    /// Returns a list of formulae in [Geometric Normal Form][gnf] (GNF), equivalent to the
    /// receiver.
    ///
    /// [gnf]: ../../chase/index.html#background
    ///
    /// **Hint**: For mor information about GNF, see [Geometric Logic in Computer Science][glics]
    /// by Steve Vickers.
    ///
    /// [glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "P(x) & (Q(x) | R(x))".parse().unwrap();
    /// let gnf_to_string: Vec<String> = formula.gnf().iter().map(|f| f.to_string()).collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    pub fn gnf(&self) -> Vec<Formula> {
        self.gnf_with(&mut SkolemGenerator::new())
    }

    /// Is similar to [`Formula::gnf`] but uses an existing [`SkolemGenerator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    /// **Note**: The GNF transformation includes Skolemization.
    ///
    /// [`SkolemGenerator`]: ../transform/struct.SkolemGenerator.html
    /// [`Formula::gnf`]: ./enum.Formula.html#method.gnf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::SkolemGenerator;
    ///
    /// let mut generator = SkolemGenerator::from("s%");
    /// let formula: Formula = "P(y) -> exists x. P(x) & Q(y)".parse().unwrap();
    /// let gnf_to_string: Vec<String> = formula.gnf().iter().map(|f| f.to_string()).collect();
    /// assert_eq!(vec!["P(y) → P(sk#0(y))", "P(y) → Q(y)"], gnf_to_string);
    /// ```
    pub fn gnf_with(&self, generator: &mut SkolemGenerator) -> Vec<Formula> {
        get_disjuncts(self.cnf_with(generator))
            .into_iter()
            .map(to_implication)
            .collect()
    }
}

// a helper to merge sequents with syntactically identical bodies
fn compress_geometric(formulae: Vec<Formula>) -> Vec<Formula> {
    formulae
        .into_iter()
        .sorted_by(|f1, f2| {
            // sort sequents by their body
            match (f1, f2) {
                (Implies { left: f1, .. }, Implies { left: f2, .. }) => f1.cmp(f2),
                _ => Equal,
            }
        })
        .into_iter()
        .coalesce(|f1, f2| {
            // merge the ones with the same body:
            match f1 {
                Implies {
                    left: ref l1,
                    right: ref r1,
                } => {
                    let l_vars = l1.free_vars();
                    let r_vars = r1.free_vars();
                    // compress sequents with no free variables that show up only in head:
                    if r_vars.iter().all(|rv| l_vars.iter().any(|lv| lv == rv)) {
                        match f2 {
                            Implies {
                                left: ref l2,
                                right: ref r2,
                            } => {
                                let l_vars = l2.free_vars();
                                let r_vars = r2.free_vars();
                                if r_vars.iter().all(|rv| l_vars.iter().any(|lv| lv == rv)) {
                                    if l1 == l2 {
                                        Ok(l2.clone().implies(r1.clone().and(*r2.clone())))
                                    } else {
                                        Err((f1, f2))
                                    }
                                } else {
                                    Err((f2, f1))
                                }
                            }
                            _ => Err((f2, f1)),
                        }
                    } else {
                        Err((f1, f2))
                    }
                }
                _ => Err((f1, f2)),
            }
        })
        .map(|f| {
            // convert the head to dnf and simplify it:
            match f {
                Implies { left, right: r } => left.implies(simplify_dnf(r.dnf())),
                _ => f,
            }
        })
        .collect()
}

// Simplifies the given DNF as a helper for compress geometric.
fn simplify_dnf(formula: Formula) -> Formula {
    fn disjunct_list(formula: Formula) -> Vec<Formula> {
        match formula {
            Or { left, right } => {
                let mut lefts = disjunct_list(*left);
                let mut rights = disjunct_list(*right);
                lefts.append(&mut rights);
                lefts
            }
            _ => vec![formula],
        }
    }

    fn conjunct_list(formula: Formula) -> Vec<Formula> {
        match formula {
            And { left, right } => {
                let mut lefts = conjunct_list(*left);
                let mut rights = conjunct_list(*right);
                lefts.append(&mut rights);
                lefts
            }
            _ => vec![formula],
        }
    }

    let disjuncts: Vec<Vec<Formula>> = disjunct_list(formula)
        .into_iter()
        .map(|d| conjunct_list(d).into_iter().unique().collect())
        .collect();

    let disjuncts: Vec<Vec<Formula>> = disjuncts
        .iter()
        .filter(|d| {
            !disjuncts.iter().any(|dd| {
                (dd.len() < d.len() || (dd.len() == d.len() && dd < d))
                    && dd.iter().all(|cc| d.iter().any(|c| cc == c))
            })
        })
        .map(|d| d.clone())
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
    /// [Geometric Normal Form][gnf] (GNF).
    ///
    /// [gnf]: ../../chase/index.html#background
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

        let mut generator = SkolemGenerator::new();
        let formulae: Vec<Formula> = self
            .formulae
            .iter()
            .flat_map(|f| f.gnf_with(&mut generator))
            .collect();

        // assuming that conversion to gnf won't change the signature
        Theory::try_from(compress_geometric(formulae)).unwrap()
    }
}

#[cfg(test)]
mod test_transform {
    use super::*;
    use crate::assert_debug_strings;

    #[test]
    fn test_gnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_strings!("true -> true", formula.gnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_strings!("true -> false", formula.gnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)", formula.gnf());
        }
        {
            let formula: Formula = "x = y".parse().unwrap();
            assert_debug_strings!("true -> (x = y)", formula.gnf());
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_strings!("P(x) -> false", formula.gnf());
        }
        {
            let formula: Formula = "P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x)", formula.gnf());
        }
        {
            let formula: Formula = "P(x) & Q(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)\ntrue -> Q(x)", formula.gnf());
        }
        {
            let formula: Formula = "P(x) | Q(x)".parse().unwrap();
            assert_debug_strings!("true -> (P(x) | Q(x))", formula.gnf());
        }
        {
            let formula: Formula = "! x. P(x)".parse().unwrap();
            assert_debug_strings!("true -> P(x)", formula.gnf());
        }
        {
            let formula: Formula = "? x. P(x)".parse().unwrap();
            assert_debug_strings!("true -> P('sk#0)", formula.gnf());
        }
        {
            let formula: Formula = "P(x) & Q(x) -> P(y) | Q(y)".parse().unwrap();
            assert_debug_strings!("(P(x) & Q(x)) -> (P(y) | Q(y))", formula.gnf());
        }
        {
            let formula: Formula = "P(x) | Q(x) -> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\n\
        P(x) -> Q(y)\n\
        Q(x) -> P(y)\n\
        Q(x) -> Q(y)",
                formula.gnf(),
            );
        }
        {
            let formula: Formula = "P(x) | Q(x) <=> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings!(
                "P(x) -> P(y)\n\
        P(x) -> Q(y)\n\
        Q(x) -> P(y)\n\
        Q(x) -> Q(y)\n\
        (P(y) & Q(y)) -> (P(x) | Q(x))",
                formula.gnf(),
            );
        }
        {
            let formula: Formula = "!x. (P(x) -> ?y. Q(x,y))".parse().unwrap();
            assert_debug_strings!("P(x) -> Q(x, sk#0(x))", formula.gnf());
        }
        {
            let formula: Formula = "!x. (P(x) -> (?y. (Q(y) & R(x, y)) | ?y. (P(y) & S(x, y)))))"
                .parse()
                .unwrap();
            assert_debug_strings!(
                "P(x) -> (Q(sk#0(x)) | P(sk#1(x)))\n\
        P(x) -> (Q(sk#0(x)) | S(x, sk#1(x)))\n\
        P(x) -> (R(x, sk#0(x)) | P(sk#1(x)))\n\
        P(x) -> (R(x, sk#0(x)) | S(x, sk#1(x)))",
                formula.gnf(),
            );
        }
        {
            let formula: Formula = "!x, y. ((P(x) & Q(y)) -> (R(x, y) -> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings!("((P(x) & Q(y)) & R(x, y)) -> S(x, y)", formula.gnf());
        }
        {
            let formula: Formula = "!x, y. ((P(x) & Q(y)) <=> (R(x, y) <=> S(x, y)))"
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
                formula.gnf(),
            );
        }
        {
            let formula: Formula = "? x. P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P('sk#0) -> Q('sk#0)", formula.gnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_strings!("P(x`) -> Q(x)", formula.gnf());
        }
        {
            let formula: Formula = "? x. (P(x) -> Q(x))".parse().unwrap();
            assert_debug_strings!("P('sk#0) -> Q('sk#0)", formula.gnf());
        }
        {
            let formula: Formula = "false -> P(x)".parse().unwrap();
            assert_debug_strings!("true -> true", formula.gnf());
        }
    }

    #[test]
    fn test_gnf_theory() {
        // mostly testing if compression of heads works properly:
        {
            let theory: Theory = "P('a); P('b);".parse().unwrap();
            assert_debug_strings!("true -> (P('a) & P('b))", theory.gnf().formulae);
        }
        {
            let theory: Theory = "P('a); P(x);".parse().unwrap();
            assert_debug_strings!("true -> P(x)\ntrue -> P('a)", theory.gnf().formulae);
        }
        {
            let theory: Theory = "P('a); P(x); P('b);".parse().unwrap();
            assert_debug_strings!(
                "true -> P(x)\ntrue -> (P(\'a) & P(\'b))",
                theory.gnf().formulae,
            );
        }
        {
            let theory: Theory = "(T() and V()) or (U() and V());".parse().unwrap();
            assert_debug_strings!("true -> ((T() & V()) | (U() & V()))", theory.gnf().formulae);
        }
    }
}
