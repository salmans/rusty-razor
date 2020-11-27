/*! Implements conversion to Prenex Normal Form (PNF) for formula.*/

use super::TermBased;
use crate::syntax::{FOF::*, *};

/// Is a wrapper around [`FOF`] that represents a formula in Prenex Normal Form (PNF).
///
/// **Hint**: A PNF is a first-order formula with all quantifiers (existential and
/// universal) and bound variables at the front, followed by a quantifier-free part.
///
/// [`FOF`]: crate::syntax::FOF
#[derive(Clone, Debug)]
pub struct PNF(FOF);

impl PNF {
    /// Returns a reference to the first-order formula wrapped in the receiver PNF.
    #[inline(always)]
    pub fn formula(&self) -> &FOF {
        &self.0
    }
}

impl From<PNF> for FOF {
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
fn binary_helper(vars: &[V], formula: &FOF, other: &FOF) -> (Vec<V>, FOF) {
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
fn pnf(formula: &FOF) -> FOF {
    match formula {
        Top | Bottom | Atom { .. } | Equals { .. } => formula.clone(),
        // e.g. ~(Qx. P(x)) -> Q' x. ~P(x)
        Not(this) => match pnf(this.formula()) {
            Forall(forall) => exists(
                forall.variables().to_vec(),
                pnf(&not(forall.formula().clone())),
            ),
            Exists(exists) => forall(
                exists.variables().to_vec(),
                pnf(&not(exists.formula().clone())),
            ),
            f => not(f),
        },
        // e.g. (Q x. F(x)) & G(y) => Q x'. F(x') & G(y) or F(x) & (Q y. G(y)) => Q y'. F(x) & G(y')
        And(this) => {
            let left = pnf(this.left());
            let right = pnf(this.right());

            if let Forall(f) = left {
                let (vars, fmla) = binary_helper(&f.variables(), f.formula(), &right);
                pnf(&forall(vars, fmla.and(right)))
            } else if let Exists(e) = left {
                let (vars, fmla) = binary_helper(e.variables(), e.formula(), &right);
                pnf(&exists(vars, fmla.and(right)))
            } else if let Forall(f) = right {
                let (vars, fmla) = binary_helper(f.variables(), f.formula(), &left);
                pnf(&forall(vars, left.and(fmla)))
            } else if let Exists(e) = right {
                let (vars, fmla) = binary_helper(e.variables(), e.formula(), &left);
                pnf(&exists(vars, left.and(fmla)))
            } else {
                left.and(right)
            }
        }
        // e.g. (Q x. F(x)) | G(y) => Q x'. F(x') | G(y) or F(x) | (Q y. G(y)) => Q y'. F(x) | G(y')
        Or(this) => {
            let left = pnf(this.left());
            let right = pnf(this.right());

            if let Forall(f) = left {
                let (vars, fmla) = binary_helper(f.variables(), f.formula(), &right);
                pnf(&forall(vars, fmla.or(right)))
            } else if let Exists(e) = left {
                let (vars, fmla) = binary_helper(e.variables(), e.formula(), &right);
                pnf(&exists(vars, fmla.or(right)))
            } else if let Forall(f) = right {
                let (vars, fmla) = binary_helper(f.variables(), f.formula(), &left);
                pnf(&forall(vars, left.or(fmla)))
            } else if let Exists(e) = right {
                let (vars, fmla) = binary_helper(e.variables(), e.formula(), &left);
                pnf(&exists(vars, left.or(fmla)))
            } else {
                left.or(right)
            }
        }
        // e.g. (Q x. F(x)) -> G(y) => Q' x'. F(x') -> G(y) or F(x) -> (Q y. G(y)) => Q' y'. F(x) -> G(y')
        Implies(this) => {
            let left = pnf(this.premise());
            let right = pnf(this.consequence());

            if let Forall(f) = left {
                let (vars, fmla) = binary_helper(f.variables(), f.formula(), &right);
                pnf(&exists(vars, fmla.implies(right)))
            } else if let Exists(e) = left {
                let (vars, fmla) = binary_helper(e.variables(), e.formula(), &right);
                pnf(&forall(vars, fmla.implies(right)))
            } else if let Forall(f) = right {
                let (vars, fmla) = binary_helper(f.variables(), f.formula(), &left);
                pnf(&forall(vars, left.implies(fmla)))
            } else if let Exists(e) = right {
                let (vars, fmla) = binary_helper(e.variables(), e.formula(), &left);
                pnf(&exists(vars, left.implies(fmla)))
            } else {
                left.implies(right)
            }
        }
        Iff(this) => {
            let left = this.left();
            let right = this.right();
            let left_to_right = left.clone().implies(right.clone());
            let right_to_left = right.clone().implies(left.clone());
            pnf(&left_to_right.and(right_to_left))
        }
        Exists(this) => exists(this.variables().to_vec(), pnf(this.formula())),
        Forall(this) => forall(this.variables().to_vec(), pnf(this.formula())),
    }
}

impl FOF {
    /// Transforms the receiver first-order formula to a Prenex Normal Form (PNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "Q(x, y) → ∃ x, y. P(x, y)".parse().unwrap();
    /// let pnf = formula.pnf();
    ///
    /// assert_eq!("∃ x`, y`. (Q(x, y) → P(x`, y`))", FOF::from(pnf).to_string());
    /// ```
    pub fn pnf(&self) -> PNF {
        PNF(pnf(self))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_debug_string, fof, pred, term, v, v_1};

    fn pnf(formula: &FOF) -> FOF {
        formula.pnf().into()
    }

    #[test]
    fn test_pnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_string!("true", pnf(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_string!("false", pnf(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", pnf(&formula));
        }

        {
            let formula: FOF = "x = y".parse().unwrap();
            assert_debug_string!("x = y", pnf(&formula));
        }
        {
            let formula: FOF = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("P(x) -> Q(y)", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("(P(x) -> Q(y)) & (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: FOF = "? x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string!("? x. ((P(x) & (~Q(y))) | R(z))", pnf(&formula));
        }
        {
            let formula: FOF = "! x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string!("! x. ((P(x) & (~Q(y))) | R(z))", pnf(&formula));
        }
        // sanity checking:
        {
            let formula: FOF = "~? x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (~P(x))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) & Q(y))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) & Q(y))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) & Q(x))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) & Q(x))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) & Q(x, y))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) & Q(x, y))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(y) & ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) & P(x))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(y) & ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) & P(x))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x) & ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) & P(x`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x) & ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) & P(x`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x, y) & ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) & P(x`, y`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x, y) & ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) & P(x`, y`))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) | Q(y))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) | Q(y))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) | Q(x))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) | Q(x))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) | Q(x, y))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) | Q(x, y))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(y) | ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) | P(x))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(y) | ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) | P(x))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x) | ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) | P(x`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x) | ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) | P(x`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x, y) | ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) | P(x`, y`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x, y) | ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) | P(x`, y`))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) -> Q(y))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) -> Q(y))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) -> Q(x))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) -> Q(x))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) -> Q(x, y))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) -> Q(x, y))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(y) -> ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(y) -> ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x) -> ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) -> P(x`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x) -> ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) -> P(x`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x, y) -> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) -> P(x`, y`))", pnf(&formula));
        }
        {
            let formula: FOF = "Q(x, y) -> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) -> P(x`, y`))", pnf(&formula));
        }

        {
            let formula: FOF = "(! x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "(? x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "(! x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string!(
                "? x`. (! x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "(? x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string!(
                "! x`. (? x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "(! x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string!(
                "? x`, y`. (! x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "(? x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string!(
                "! x`, y`. (? x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "Q(y) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "Q(y) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "Q(x) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string!(
                "! x`. (? x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "Q(x) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string!(
                "? x`. (! x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "Q(x, y) <=> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!(
                "! x`, y`. (? x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "Q(x, y) <=> ? x, y. P(x, y)".parse().unwrap();
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
            pnf(&exists(vec![v!(x)], fof!(P(x))).and(pred!(Q).app(vec![term!(x), v_1!(x).into()]))),
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) & Q(x))",
            pnf(&exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()])).and(fof!(Q(x)))),
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
            let formula: FOF = "(! x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(? x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: FOF = "(! x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. (? x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "(! x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "? x. (? x`. (! x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "(? x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "! x. (! x`. (? x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "(? x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. (! x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        // multiple steps
        {
            let formula: FOF = "~~?x.P(x)".parse().unwrap();
            assert_debug_string!("? x. (~(~P(x)))", pnf(&formula));
        }
        {
            let formula: FOF = "~~!x.P(x)".parse().unwrap();
            assert_debug_string!("! x. (~(~P(x)))", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) & ((! x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) & (Q(x`) & R(x)))", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) & ((? x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) & (Q(x`) & R(x)))", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ((! x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) | (Q(x`) | R(x)))", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ((? x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) | (Q(x`) | R(x)))", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> ((! x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) -> (Q(x`) -> R(x)))", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> ((? x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) -> (Q(x`) -> R(x)))", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> ((! x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string!("? x`. (! x``. (! x```. (? x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", pnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> ((? x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string!("! x`. (? x``. (? x```. (! x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", pnf(&formula));
        }
        // random formulae
        {
            let formula: FOF = "!x . (P(x) -> ?y . (P(y) & Q(x, y)))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) -> (P(y) & Q(x, y))))", pnf(&formula));
        }
        {
            let formula: FOF = "?x . (P(x) & !y . (P(y) -> Q(x, y)))".parse().unwrap();
            assert_debug_string!("? x. (! y. (P(x) & (P(y) -> Q(x, y))))", pnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> ~(!y . (P(y) -> Q(x, y))))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) -> (~(P(y) -> Q(x, y)))))", pnf(&formula));
        }
        {
            let formula: FOF = "(P() | ? x. Q(x)) -> !z. R(z)".parse().unwrap();
            assert_debug_string!("! x. (! z. ((P() | Q(x)) -> R(z)))", pnf(&formula));
        }
        {
            let formula: FOF = "!x.?y.(!z.Q(x) & ~?x.R(x)) | (~Q(y) -> !w. R(y))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "! x. (? y. (! z. (! x`. (! w. ((Q(x) & (~R(x`))) | ((~Q(y)) -> R(y)))))))",
                pnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (!y. P(x, y) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string!("! x. (! y. (? y`. (P(x, y) -> Q(x, y`))))", pnf(&formula));
        }
        {
            let formula: FOF = "!x. ((!y. P(x, y)) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (? y`. (P(x, y) -> Q(x, y`))))", pnf(&formula));
        }
    }
}
