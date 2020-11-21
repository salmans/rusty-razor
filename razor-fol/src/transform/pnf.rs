/*! Implements conversion to Prenex Normal Form (PNF) for formula.*/

use super::TermBased;
use crate::syntax::{Formula::*, *};

/// Is a wrapper around [`Formula`] that represents a formula in Prenex Normal Form (PNF).
///
/// **Hint**: A PNF is a formula with all quantifiers (existential and universal) and bound
/// variables at the front, followed by a quantifier-free part.
///
/// [`Formula`]: ../syntax/enum.Formula.html
#[derive(Clone, Debug)]
pub struct PNF(Formula);

impl PNF {
    /// Returns a reference to the formula wrapped in the receiver PNF.
    #[inline(always)]
    pub fn formula(&self) -> &Formula {
        &self.0
    }
}

impl From<PNF> for Formula {
    fn from(pnf: PNF) -> Self {
        pnf.0
    }
}

// Appends a postfix to the input variable until the result is not no longer in the list of
// no collision variables.
fn rename(variable: &V, no_collision_variables: &[&V]) -> V {
    let mut name = variable.0.clone();
    let names: Vec<_> = no_collision_variables.iter().map(|v| &v.0).collect();
    while names.contains(&&name) {
        name.push('`')
    }
    V::from(&name)
}

// helper for transforming formulae with binary operands
#[inline]
fn binary_helper(vars: &[V], formula: &Formula, other: &Formula) -> (Vec<V>, Formula) {
    let formula_vars = formula.free_vars();
    let other_vars = other.free_vars();

    let intersect: Vec<&V> = vars.iter().filter(|v| other_vars.contains(v)).collect();
    let union = {
        let mut union = Vec::new();
        union.extend(vars.iter());
        union.extend(formula_vars);
        union.extend(other_vars);
        union
    };

    let renaming = |v: &V| {
        if intersect.contains(&v) {
            rename(v, &union)
        } else {
            v.clone()
        }
    };
    let vars: Vec<V> = vars.iter().map(&renaming).collect();
    let fmla = formula.rename_vars(&renaming);

    (vars, fmla)
}

// The transforming function as a helper
#[inline]
fn pnf(formula: &Formula) -> Formula {
    match formula {
        Top | Bottom | Atom { .. } | Equals { .. } => formula.clone(),
        // e.g. ~(Qx. P(x)) -> Q' x. ~P(x)
        Not { formula: fmla } => match pnf(fmla) {
            Forall { variables, formula } => exists(variables, pnf(&not(*formula))),
            Exists { variables, formula } => forall(variables, pnf(&not(*formula))),
            f => not(f),
        },
        // e.g. (Q x. F(x)) & G(y) => Q x'. F(x') & G(y) or F(x) & (Q y. G(y)) => Q y'. F(x) & G(y')
        And { left, right } => {
            let left = pnf(left);
            let right = pnf(right);

            if let Forall { variables, formula } = left {
                let (vars, fmla) = binary_helper(&variables, &formula, &right);
                pnf(&forall(vars, fmla.and(right)))
            } else if let Exists { variables, formula } = left {
                let (vars, fmla) = binary_helper(&variables, &formula, &right);
                pnf(&exists(vars, fmla.and(right)))
            } else if let Forall { variables, formula } = right {
                let (vars, fmla) = binary_helper(&variables, &formula, &left);
                pnf(&forall(vars, left.and(fmla)))
            } else if let Exists { variables, formula } = right {
                let (vars, fmla) = binary_helper(&variables, &formula, &left);
                pnf(&exists(vars, left.and(fmla)))
            } else {
                left.and(right)
            }
        }
        // e.g. (Q x. F(x)) | G(y) => Q x'. F(x') | G(y) or F(x) | (Q y. G(y)) => Q y'. F(x) | G(y')
        Or { left, right } => {
            let left = pnf(left);
            let right = pnf(right);

            if let Forall { variables, formula } = left {
                let (vars, fmla) = binary_helper(&variables, &formula, &right);
                pnf(&forall(vars, fmla.or(right)))
            } else if let Exists { variables, formula } = left {
                let (vars, fmla) = binary_helper(&variables, &formula, &right);
                pnf(&exists(vars, fmla.or(right)))
            } else if let Forall { variables, formula } = right {
                let (vars, fmla) = binary_helper(&variables, &formula, &left);
                pnf(&forall(vars, left.or(fmla)))
            } else if let Exists { variables, formula } = right {
                let (vars, fmla) = binary_helper(&variables, &formula, &left);
                pnf(&exists(vars, left.or(fmla)))
            } else {
                left.or(right)
            }
        }
        // e.g. (Q x. F(x)) -> G(y) => Q' x'. F(x') -> G(y) or F(x) -> (Q y. G(y)) => Q' y'. F(x) -> G(y')
        Implies { left, right } => {
            let left = pnf(left);
            let right = pnf(right);

            if let Forall { variables, formula } = left {
                let (vars, fmla) = binary_helper(&variables, &formula, &right);
                pnf(&exists(vars, fmla.implies(right)))
            } else if let Exists { variables, formula } = left {
                let (vars, fmla) = binary_helper(&variables, &formula, &right);
                pnf(&forall(vars, fmla.implies(right)))
            } else if let Forall { variables, formula } = right {
                let (vars, fmla) = binary_helper(&variables, &formula, &left);
                pnf(&forall(vars, left.implies(fmla)))
            } else if let Exists { variables, formula } = right {
                let (vars, fmla) = binary_helper(&variables, &formula, &left);
                pnf(&exists(vars, left.implies(fmla)))
            } else {
                left.implies(right)
            }
        }
        Iff { left, right } => {
            let left_to_right = left.clone().implies(*right.clone());
            let right_to_left = right.clone().implies(*left.clone());
            pnf(&left_to_right.and(right_to_left))
        }
        Exists { variables, formula } => exists(variables.clone(), pnf(&formula)),
        Forall { variables, formula } => forall(variables.clone(), pnf(&formula)),
    }
}

impl Formula {
    /// Transforms the receiver formula to a Prenex Normal Form (PNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "Q(x, y) → ∃ x, y. P(x, y)".parse().unwrap();
    /// let pnf = formula.pnf();
    ///
    /// assert_eq!("∃ x`, y`. (Q(x, y) → P(x`, y`))", Formula::from(pnf).to_string());
    /// ```
    pub fn pnf(&self) -> PNF {
        PNF(pnf(self))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_debug_string, formula, pred, term, v, v_1};

    fn pnf(formula: &Formula) -> Formula {
        formula.pnf().into()
    }

    #[test]
    fn test_pnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string!("true", pnf(&formula));
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string!("false", pnf(&formula));
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", pnf(&formula));
        }

        {
            let formula: Formula = "x = y".parse().unwrap();
            assert_debug_string!("x = y", pnf(&formula));
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("P(x) -> Q(y)", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("(P(x) -> Q(y)) & (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: Formula = "? x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string!("? x. ((P(x) & (~Q(y))) | R(z))", pnf(&formula));
        }
        {
            let formula: Formula = "! x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string!("! x. ((P(x) & (~Q(y))) | R(z))", pnf(&formula));
        }
        // sanity checking:
        {
            let formula: Formula = "~? x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (~P(x))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) & Q(y))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) & Q(y))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) & Q(x))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) & Q(x))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) & Q(x, y))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) & Q(x, y))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(y) & ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) & P(x))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(y) & ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) & P(x))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x) & ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) & P(x`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x) & ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) & P(x`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x, y) & ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) & P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x, y) & ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) & P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) | Q(y))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) | Q(y))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) | Q(x))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) | Q(x))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) | Q(x, y))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) | Q(x, y))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(y) | ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) | P(x))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(y) | ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) | P(x))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x) | ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) | P(x`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x) | ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) | P(x`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x, y) | ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) | P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x, y) | ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) | P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) -> Q(y))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) -> Q(y))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) -> Q(x))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) -> Q(x))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) -> Q(x, y))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) -> Q(x, y))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(y) -> ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(y) -> ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x) -> ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) -> P(x`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x) -> ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) -> P(x`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x, y) -> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) -> P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Formula = "Q(x, y) -> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) -> P(x`, y`))", pnf(&formula));
        }

        {
            let formula: Formula = "(! x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "(! x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string!(
                "? x`. (! x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string!(
                "! x`. (? x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string!(
                "? x`, y`. (! x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string!(
                "! x`, y`. (? x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "Q(y) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "Q(y) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "Q(x) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string!(
                "! x`. (? x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "Q(x) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string!(
                "? x`. (! x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "Q(x, y) <=> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!(
                "! x`, y`. (? x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "Q(x, y) <=> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!(
                "? x`, y`. (! x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                pnf(&formula),
            );
        }
        //renaming tests
        assert_debug_string!(
            "! x``, x`. (P(x``) & Q(x))",
            pnf(&forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .and(pred!(Q).app(vec![term!(x)]))),
        );
        assert_debug_string!(
            "? x``, x`. (P(x``) & Q(x))",
            pnf(&exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .and(pred!(Q).app(vec![term!(x)]))),
        );
        assert_debug_string!(
            "? x``. (P(x``) & Q(x, x`))",
            pnf(&exists(vec![v!(x)], formula!(P(x)))
                .and(pred!(Q).app(vec![term!(x), v_1!(x).into()]))),
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) & Q(x))",
            pnf(
                &exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                    .and(formula!(Q(x)))
            ),
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) & P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x)])
                .and(forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))),
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) & P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x)])
                .and(exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))),
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) & P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .and(exists(vec![v!(x)], pred!(P).app(vec![term!(x)])))),
        );
        assert_debug_string!(
            "? x``. (Q(x) & P(x``, x`))",
            pnf(&pred!(Q).app(vec![term!(x)]).and(exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]),
            ))),
        );

        assert_debug_string!(
            "! x``, x`. (P(x``) | Q(x))",
            pnf(&forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .or(pred!(Q).app(vec![term!(x)]))),
        );
        assert_debug_string!(
            "? x``, x`. (P(x``) | Q(x))",
            pnf(&exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .or(pred!(Q).app(vec![term!(x)])))
        );
        assert_debug_string!(
            "? x``. (P(x``) | Q(x, x`))",
            pnf(&exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .or(pred!(Q).app(vec![term!(x), v_1!(x).into()])))
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) | Q(x))",
            pnf(
                &exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                    .or(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) | P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x)])
                .or(forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) | P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x)])
                .or(exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) | P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .or(exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (Q(x) | P(x``, x`))",
            pnf(&pred!(Q).app(vec![term!(x)]).or(exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]),
            )))
        );

        assert_debug_string!(
            "? x``, x`. (P(x``) -> Q(x))",
            pnf(&forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .implies(pred!(Q).app(vec![term!(x)])))
        );
        assert_debug_string!(
            "! x``, x`. (P(x``) -> Q(x))",
            pnf(&exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .implies(pred!(Q).app(vec![term!(x)])))
        );
        assert_debug_string!(
            "! x``. (P(x``) -> Q(x, x`))",
            pnf(&exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .implies(pred!(Q).app(vec![term!(x), v_1!(x).into()])))
        );
        assert_debug_string!(
            "! x``. (P(x``, x`) -> Q(x))",
            pnf(
                &exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                    .implies(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) -> P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x)])
                .implies(forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) -> P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x)])
                .implies(exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) -> P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .implies(exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (Q(x) -> P(x``, x`))",
            pnf(&pred!(Q).app(vec![term!(x)]).implies(exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]),
            )))
        );

        assert_debug_string!(
            "? x``, x`. (! x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            pnf(&forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .iff(pred!(Q).app(vec![term!(x)])))
        );
        assert_debug_string!(
            "! x``, x`. (? x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            pnf(&exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .iff(pred!(Q).app(vec![term!(x)])))
        );
        assert_debug_string!(
            "! x``. (? x```. ((P(x``) -> Q(x, x`)) & (Q(x, x`) -> P(x```))))",
            pnf(&exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .iff(pred!(Q).app(vec![term!(x), v_1!(x).into()])))
        );
        assert_debug_string!(
            "! x``. (? x```. ((P(x``, x`) -> Q(x)) & (Q(x) -> P(x```, x`))))",
            pnf(
                &exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                    .iff(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``, x`. (? x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            pnf(&pred!(Q)
                .app(vec![term!(x)])
                .iff(forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``, x`. (! x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            pnf(&pred!(Q)
                .app(vec![term!(x)])
                .iff(exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (! x```. ((Q(x, x`) -> P(x``)) & (P(x```) -> Q(x, x`))))",
            pnf(&pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .iff(exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (! x```. ((Q(x) -> P(x``, x`)) & (P(x```, x`) -> Q(x))))",
            pnf(&pred!(Q).app(vec![term!(x)]).iff(exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]),
            )))
        );
        // both sides of binary formulae
        {
            let formula: Formula = "(! x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(? x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: Formula = "(! x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. (? x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "(! x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "? x. (? x`. (! x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "! x. (! x`. (? x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. (! x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        // multiple steps
        {
            let formula: Formula = "~~?x.P(x)".parse().unwrap();
            assert_debug_string!("? x. (~(~P(x)))", pnf(&formula));
        }
        {
            let formula: Formula = "~~!x.P(x)".parse().unwrap();
            assert_debug_string!("! x. (~(~P(x)))", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) & ((! x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) & (Q(x`) & R(x)))", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) & ((? x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) & (Q(x`) & R(x)))", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) | ((! x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) | (Q(x`) | R(x)))", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) | ((? x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) | (Q(x`) | R(x)))", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) -> ((! x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) -> (Q(x`) -> R(x)))", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) -> ((? x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) -> (Q(x`) -> R(x)))", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) <=> ((! x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string!("? x`. (! x``. (! x```. (? x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", pnf(&formula));
        }
        {
            let formula: Formula = "P(x) <=> ((? x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string!("! x`. (? x``. (? x```. (! x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", pnf(&formula));
        }
        // random formulae
        {
            let formula: Formula = "!x . (P(x) -> ?y . (P(y) & Q(x, y)))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) -> (P(y) & Q(x, y))))", pnf(&formula));
        }
        {
            let formula: Formula = "?x . (P(x) & !y . (P(y) -> Q(x, y)))".parse().unwrap();
            assert_debug_string!("? x. (! y. (P(x) & (P(y) -> Q(x, y))))", pnf(&formula));
        }
        {
            let formula: Formula = "!x. (P(x) -> ~(!y . (P(y) -> Q(x, y))))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) -> (~(P(y) -> Q(x, y)))))", pnf(&formula));
        }
        {
            let formula: Formula = "(P() | ? x. Q(x)) -> !z. R(z)".parse().unwrap();
            assert_debug_string!("! x. (! z. ((P() | Q(x)) -> R(z)))", pnf(&formula));
        }
        {
            let formula: Formula = "!x.?y.(!z.Q(x) & ~?x.R(x)) | (~Q(y) -> !w. R(y))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "! x. (? y. (! z. (! x`. (! w. ((Q(x) & (~R(x`))) | ((~Q(y)) -> R(y)))))))",
                pnf(&formula),
            );
        }
        {
            let formula: Formula = "!x. (!y. P(x, y) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string!("! x. (! y. (? y`. (P(x, y) -> Q(x, y`))))", pnf(&formula));
        }
        {
            let formula: Formula = "!x. ((!y. P(x, y)) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (? y`. (P(x, y) -> Q(x, y`))))", pnf(&formula));
        }
    }
}
