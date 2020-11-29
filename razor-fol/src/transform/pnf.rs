/*! Defines Prenex Normal Form (PNF) formulae and implements an algorithm for converting
a [`FOF`] to [`PNF`].

[`FOF`]: crate::syntax::FOF
*/
use super::{Substitution, TermBased, VariableRenaming};
use crate::syntax::{formula::*, Term, FOF, V};

/// Represents a formula in Prenex Normal Form (PNF).
///
/// **Hint**: A PNF is a first-order formula with all quantifiers (existential and
/// universal) and bound variables at the front, followed by a quantifier-free part.
#[derive(Clone, Debug)]
pub enum PNF {
    /// Is the quantifier-free portion of a [`PNF`].
    QuantifierFree(QFF),

    /// Is an existentially quantified formula, wrapping an [`Exists`].
    Exists(Box<Exists<PNF>>),

    /// Is a universally quantified formula, wrapping a [`Forall`].
    Forall(Box<Forall<PNF>>),
}

impl From<Atom> for PNF {
    fn from(value: Atom) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Equals> for PNF {
    fn from(value: Equals) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Not<QFF>> for PNF {
    fn from(value: Not<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<And<QFF>> for PNF {
    fn from(value: And<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Or<QFF>> for PNF {
    fn from(value: Or<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Implies<QFF>> for PNF {
    fn from(value: Implies<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Iff<QFF>> for PNF {
    fn from(value: Iff<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Exists<PNF>> for PNF {
    fn from(value: Exists<PNF>) -> Self {
        Self::Exists(Box::new(value))
    }
}

impl From<Forall<PNF>> for PNF {
    fn from(value: Forall<PNF>) -> Self {
        Self::Forall(Box::new(value))
    }
}

impl From<QFF> for PNF {
    fn from(value: QFF) -> Self {
        Self::QuantifierFree(value)
    }
}

impl From<&FOF> for PNF {
    fn from(value: &FOF) -> Self {
        pnf(value)
    }
}

impl PNF {
    fn not(formula: QFF) -> Self {
        Not { formula }.into()
    }

    fn exists(variables: Vec<V>, formula: Self) -> Self {
        Exists { variables, formula }.into()
    }

    fn forall(variables: Vec<V>, formula: Self) -> Self {
        Forall { variables, formula }.into()
    }
}

impl Formula for PNF {
    fn free_vars(&self) -> Vec<&V> {
        match self {
            PNF::QuantifierFree(this) => this.free_vars(),
            PNF::Exists(this) => this.free_vars(),
            PNF::Forall(this) => this.free_vars(),
        }
    }
}

impl TermBased for PNF {
    #[inline]
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        match self {
            PNF::QuantifierFree(this) => this.transform(f).into(),
            PNF::Exists(this) => Exists {
                variables: this.variables.clone(),
                formula: this.formula.transform(f),
            }
            .into(),
            PNF::Forall(this) => Forall {
                variables: this.variables.clone(),
                formula: this.formula.transform(f),
            }
            .into(),
        }
    }

    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self {
        self.transform(&|t: &Term| t.rename_vars(renaming))
    }

    fn substitute(&self, substitution: &impl Substitution) -> Self {
        self.transform(&|t: &Term| t.substitute(substitution))
    }
}

impl From<PNF> for FOF {
    fn from(value: PNF) -> Self {
        match value {
            PNF::QuantifierFree(this) => this.into(),
            PNF::Exists(this) => FOF::exists(this.variables, this.formula.into()),
            PNF::Forall(this) => FOF::forall(this.variables, this.formula.into()),
        }
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
fn binary_helper(vars: &[V], formula: &PNF, other: &PNF) -> (Vec<V>, PNF) {
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
fn pnf(formula: &FOF) -> PNF {
    match formula {
        FOF::Top => PNF::QuantifierFree(QFF::Top),
        FOF::Bottom => PNF::QuantifierFree(QFF::Bottom),
        FOF::Atom(this) => this.clone().into(),
        FOF::Equals(this) => this.clone().into(),
        // e.g. ~(Qx. P(x)) -> Q' x. ~P(x)
        FOF::Not(this) => match pnf(&this.formula) {
            PNF::Forall(forall) => {
                PNF::exists(forall.variables, pnf(&FOF::not(forall.formula.into())))
            }
            PNF::Exists(exists) => {
                PNF::forall(exists.variables, pnf(&FOF::not(exists.formula.into())))
            }
            PNF::QuantifierFree(this) => PNF::not(this),
        },
        // e.g. (Q x. F(x)) & G(y) => Q x'. F(x') & G(y) or F(x) & (Q y. G(y)) => Q y'. F(x) & G(y')
        FOF::And(this) => {
            let left = pnf(&this.left);
            let right = pnf(&this.right);

            match (&left, &right) {
                (PNF::Forall(f), _) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &right);
                    pnf(&FOF::forall(vars, FOF::from(fmla).and(right.into())))
                }
                (PNF::Exists(e), _) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &right);
                    pnf(&FOF::exists(vars, FOF::from(fmla).and(right.into())))
                }
                (_, PNF::Forall(f)) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &left);
                    pnf(&FOF::forall(vars, FOF::from(left).and(fmla.into())))
                }
                (_, PNF::Exists(e)) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &left);
                    pnf(&FOF::exists(vars, FOF::from(left).and(fmla.into())))
                }
                (PNF::QuantifierFree(left), PNF::QuantifierFree(right)) => And {
                    left: left.clone(),
                    right: right.clone(),
                }
                .into(),
            }
        }
        // e.g. (Q x. F(x)) | G(y) => Q x'. F(x') | G(y) or F(x) | (Q y. G(y)) => Q y'. F(x) | G(y')
        FOF::Or(this) => {
            let left = pnf(&this.left);
            let right = pnf(&this.right);

            match (&left, &right) {
                (PNF::Forall(f), _) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &right);
                    pnf(&FOF::forall(vars, FOF::from(fmla).or(right.into())))
                }
                (PNF::Exists(e), _) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &right);
                    pnf(&FOF::exists(vars, FOF::from(fmla).or(right.into())))
                }
                (_, PNF::Forall(f)) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &left);
                    pnf(&FOF::forall(vars, FOF::from(left).or(fmla.into())))
                }
                (_, PNF::Exists(e)) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &left);
                    pnf(&FOF::exists(vars, FOF::from(left).or(fmla.into())))
                }
                (PNF::QuantifierFree(left), PNF::QuantifierFree(right)) => Or {
                    left: left.clone(),
                    right: right.clone(),
                }
                .into(),
            }
        }
        // e.g. (Q x. F(x)) -> G(y) => Q' x'. F(x') -> G(y) or F(x) -> (Q y. G(y)) => Q' y'. F(x) -> G(y')
        FOF::Implies(this) => {
            let premise = pnf(&this.premise);
            let consequence = pnf(&this.consequence);

            match (&premise, &consequence) {
                (PNF::Forall(f), _) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &consequence);
                    pnf(&FOF::exists(
                        vars,
                        FOF::from(fmla).implies(consequence.into()),
                    ))
                }
                (PNF::Exists(e), _) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &consequence);
                    pnf(&FOF::forall(
                        vars,
                        FOF::from(fmla).implies(consequence.into()),
                    ))
                }
                (_, PNF::Forall(f)) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &premise);
                    pnf(&FOF::forall(vars, FOF::from(premise).implies(fmla.into())))
                }
                (_, PNF::Exists(e)) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &premise);
                    pnf(&FOF::exists(vars, FOF::from(premise).implies(fmla.into())))
                }
                (PNF::QuantifierFree(premise), PNF::QuantifierFree(consequence)) => Implies {
                    premise: premise.clone(),
                    consequence: consequence.clone(),
                }
                .into(),
            }
        }
        FOF::Iff(this) => {
            let left = &this.left;
            let right = &this.right;
            let left_to_right = left.clone().implies(right.clone());
            let right_to_left = right.clone().implies(left.clone());
            pnf(&left_to_right.and(right_to_left))
        }
        FOF::Exists(this) => PNF::exists(this.variables.clone(), pnf(&this.formula)),
        FOF::Forall(this) => PNF::forall(this.variables.clone(), pnf(&this.formula)),
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
        self.into()
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
            pnf(
                &FOF::forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                    .and(pred!(Q).app(vec![term!(x)]))
            ),
        );
        assert_debug_string!(
            "? x``, x`. (P(x``) & Q(x))",
            pnf(
                &FOF::exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                    .and(pred!(Q).app(vec![term!(x)]))
            ),
        );
        assert_debug_string!(
            "? x``. (P(x``) & Q(x, x`))",
            pnf(&FOF::exists(vec![v!(x)], fof!(P(x)))
                .and(pred!(Q).app(vec![term!(x), v_1!(x).into()]))),
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) & Q(x))",
            pnf(
                &FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                    .and(fof!(Q(x)))
            ),
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) & P(x``))",
            pnf(&pred!(Q).app(vec![term!(x)]).and(FOF::forall(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)])
            ))),
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) & P(x``))",
            pnf(&pred!(Q).app(vec![term!(x)]).and(FOF::exists(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)])
            ))),
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) & P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .and(FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x)])))),
        );
        assert_debug_string!(
            "? x``. (Q(x) & P(x``, x`))",
            pnf(&pred!(Q).app(vec![term!(x)]).and(FOF::exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]),
            ))),
        );

        assert_debug_string!(
            "! x``, x`. (P(x``) | Q(x))",
            pnf(
                &FOF::forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                    .or(pred!(Q).app(vec![term!(x)]))
            ),
        );
        assert_debug_string!(
            "? x``, x`. (P(x``) | Q(x))",
            pnf(
                &FOF::exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                    .or(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "? x``. (P(x``) | Q(x, x`))",
            pnf(&FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .or(pred!(Q).app(vec![term!(x), v_1!(x).into()])))
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) | Q(x))",
            pnf(
                &FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                    .or(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) | P(x``))",
            pnf(&pred!(Q).app(vec![term!(x)]).or(FOF::forall(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)])
            )))
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) | P(x``))",
            pnf(&pred!(Q).app(vec![term!(x)]).or(FOF::exists(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)])
            )))
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) | P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .or(FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (Q(x) | P(x``, x`))",
            pnf(&pred!(Q).app(vec![term!(x)]).or(FOF::exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]),
            )))
        );

        assert_debug_string!(
            "? x``, x`. (P(x``) -> Q(x))",
            pnf(
                &FOF::forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                    .implies(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``, x`. (P(x``) -> Q(x))",
            pnf(
                &FOF::exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                    .implies(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``. (P(x``) -> Q(x, x`))",
            pnf(&FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .implies(pred!(Q).app(vec![term!(x), v_1!(x).into()])))
        );
        assert_debug_string!(
            "! x``. (P(x``, x`) -> Q(x))",
            pnf(
                &FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                    .implies(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) -> P(x``))",
            pnf(&pred!(Q).app(vec![term!(x)]).implies(FOF::forall(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)])
            )))
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) -> P(x``))",
            pnf(&pred!(Q).app(vec![term!(x)]).implies(FOF::exists(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)])
            )))
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) -> P(x``))",
            pnf(&pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .implies(FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (Q(x) -> P(x``, x`))",
            pnf(&pred!(Q).app(vec![term!(x)]).implies(FOF::exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]),
            )))
        );

        assert_debug_string!(
            "? x``, x`. (! x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            pnf(
                &FOF::forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                    .iff(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``, x`. (? x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            pnf(
                &FOF::exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                    .iff(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``. (? x```. ((P(x``) -> Q(x, x`)) & (Q(x, x`) -> P(x```))))",
            pnf(&FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .iff(pred!(Q).app(vec![term!(x), v_1!(x).into()])))
        );
        assert_debug_string!(
            "! x``. (? x```. ((P(x``, x`) -> Q(x)) & (Q(x) -> P(x```, x`))))",
            pnf(
                &FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                    .iff(pred!(Q).app(vec![term!(x)]))
            )
        );
        assert_debug_string!(
            "! x``, x`. (? x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            pnf(&pred!(Q).app(vec![term!(x)]).iff(FOF::forall(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)])
            )))
        );
        assert_debug_string!(
            "? x``, x`. (! x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            pnf(&pred!(Q).app(vec![term!(x)]).iff(FOF::exists(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)])
            )))
        );
        assert_debug_string!(
            "? x``. (! x```. ((Q(x, x`) -> P(x``)) & (P(x```) -> Q(x, x`))))",
            pnf(&pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .iff(FOF::exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))))
        );
        assert_debug_string!(
            "? x``. (! x```. ((Q(x) -> P(x``, x`)) & (P(x```, x`) -> Q(x))))",
            pnf(&pred!(Q).app(vec![term!(x)]).iff(FOF::exists(
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
