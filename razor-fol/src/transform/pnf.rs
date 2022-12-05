/*! Defines formulae in Prenex Normal Form (PNF) and implements an algorithm for transforming
an [`Fof`] to a [`Pnf`].

[`Fof`]: crate::syntax::Fof
*/
use crate::syntax::{formula::qff::Qff, formula::*, term::Complex, Fof, Var};

/// Represents a formula in Prenex Normal Form (PNF).
///
/// **Hint**: A PNF is a first-order formula with all quantifiers (existential and
/// universal) and bound variables at the front, followed by a quantifier-free part.
#[derive(Clone)]
pub enum Pnf {
    /// Is the quantifier-free portion of a [`Pnf`].
    QFF(Qff),

    /// Is an existentially quantified PNF, wrapping an [`Exists`].
    Exists(Box<Exists<Pnf>>),

    /// Is a universally quantified PNF, wrapping a [`Forall`].
    Forall(Box<Forall<Pnf>>),
}

impl From<Atom<Complex>> for Pnf {
    fn from(value: Atom<Complex>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Equals<Complex>> for Pnf {
    fn from(value: Equals<Complex>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Not<Qff>> for Pnf {
    fn from(value: Not<Qff>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<And<Qff>> for Pnf {
    fn from(value: And<Qff>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Or<Qff>> for Pnf {
    fn from(value: Or<Qff>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Implies<Qff>> for Pnf {
    fn from(value: Implies<Qff>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Iff<Qff>> for Pnf {
    fn from(value: Iff<Qff>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Exists<Pnf>> for Pnf {
    fn from(value: Exists<Pnf>) -> Self {
        Self::Exists(Box::new(value))
    }
}

impl From<Forall<Pnf>> for Pnf {
    fn from(value: Forall<Pnf>) -> Self {
        Self::Forall(Box::new(value))
    }
}

impl From<Qff> for Pnf {
    fn from(value: Qff) -> Self {
        Self::QFF(value)
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`Pnf`].
pub trait ToPnf: Formula {
    /// Transforms `self` to a Prenex Normal Form (PNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Fof;
    /// use razor_fol::transform::ToPnf;    
    ///
    /// let formula: Fof = "Q(x, y) → ∃ x, y. P(x, y)".parse().unwrap();
    /// let pnf = formula.pnf();
    ///
    /// assert_eq!("∃ x`, y`. (Q(x, y) → P(x`, y`))", pnf.to_string());
    /// ```
    fn pnf(&self) -> Pnf;
}

impl ToPnf for Fof {
    fn pnf(&self) -> Pnf {
        pnf(self)
    }
}

impl<T: ToPnf> From<T> for Pnf {
    fn from(value: T) -> Self {
        value.pnf()
    }
}

impl Pnf {
    #[inline(always)]
    fn not(formula: Qff) -> Self {
        Not { formula }.into()
    }

    #[inline(always)]
    fn exists(variables: Vec<Var>, formula: Self) -> Self {
        Exists { variables, formula }.into()
    }

    #[inline(always)]
    fn forall(variables: Vec<Var>, formula: Self) -> Self {
        Forall { variables, formula }.into()
    }
}

impl Formula for Pnf {
    type Term = Complex;

    fn signature(&self) -> Result<crate::syntax::Sig, crate::syntax::Error> {
        match self {
            Pnf::QFF(this) => this.signature(),
            Pnf::Exists(this) => this.signature(),
            Pnf::Forall(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&Var> {
        match self {
            Pnf::QFF(this) => this.free_vars(),
            Pnf::Exists(this) => this.free_vars(),
            Pnf::Forall(this) => this.free_vars(),
        }
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            Pnf::QFF(this) => this.transform_term(f).into(),
            Pnf::Exists(this) => Exists {
                variables: this.variables.clone(),
                formula: this.formula.transform_term(f),
            }
            .into(),
            Pnf::Forall(this) => Forall {
                variables: this.variables.clone(),
                formula: this.formula.transform_term(f),
            }
            .into(),
        }
    }
}

impl FormulaEx for Pnf {
    fn precedence(&self) -> u8 {
        match self {
            Pnf::QFF(this) => this.precedence(),
            Pnf::Exists(this) => this.precedence(),
            Pnf::Forall(this) => this.precedence(),
        }
    }
}

impl std::fmt::Display for Pnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Fof::from(self).fmt(f)
    }
}

impl From<Pnf> for Fof {
    fn from(value: Pnf) -> Self {
        match value {
            Pnf::QFF(this) => this.into(),
            Pnf::Exists(this) => Fof::exists(this.variables, this.formula.into()),
            Pnf::Forall(this) => Fof::forall(this.variables, this.formula.into()),
        }
    }
}

impl From<&Pnf> for Fof {
    fn from(value: &Pnf) -> Self {
        value.clone().into()
    }
}

// Appends a postfix to the input variable until the result is not no longer in the list of
// no collision variables.
fn rename(variable: &Var, no_collision_variables: &[&Var]) -> Var {
    let mut name = variable.name().to_string();
    let mut names = no_collision_variables.iter().map(|v| v.name());
    while names.any(|x| x == name.as_str()) {
        name.push('`')
    }
    Var::from(&name)
}

// helper for transforming formulae with binary operands
#[inline]
fn binary_helper(vars: &[Var], formula: &Pnf, other: &Pnf) -> (Vec<Var>, Pnf) {
    let formula_vars = formula.free_vars();
    let other_vars = other.free_vars();

    let intersect: Vec<&Var> = vars.iter().filter(|v| other_vars.contains(v)).collect();
    let union = {
        let mut union = Vec::new();
        union.extend(vars.iter());
        union.extend(formula_vars);
        union.extend(other_vars);
        union
    };

    let renaming = |v: &Var| {
        if intersect.contains(&v) {
            rename(v, &union)
        } else {
            v.clone()
        }
    };
    let vars: Vec<Var> = vars.iter().map(&renaming).collect();
    let fmla = formula.rename_var(&renaming);

    (vars, fmla)
}

// The transforming function as a helper
#[inline]
fn pnf(formula: &Fof) -> Pnf {
    match formula {
        Fof::Top => Pnf::QFF(Qff::Top),
        Fof::Bottom => Pnf::QFF(Qff::Bottom),
        Fof::Atom(this) => this.clone().into(),
        Fof::Equals(this) => this.clone().into(),
        // e.g. ~(Qx. P(x)) -> Q' x. ~P(x)
        Fof::Not(this) => match pnf(&this.formula) {
            Pnf::Forall(forall) => {
                Pnf::exists(forall.variables, pnf(&Fof::not(forall.formula.into())))
            }
            Pnf::Exists(exists) => {
                Pnf::forall(exists.variables, pnf(&Fof::not(exists.formula.into())))
            }
            Pnf::QFF(this) => Pnf::not(this),
        },
        // e.g. (Q x. F(x)) & G(y) => Q x'. F(x') & G(y) or F(x) & (Q y. G(y)) => Q y'. F(x) & G(y')
        Fof::And(this) => {
            let left = pnf(&this.left);
            let right = pnf(&this.right);

            match (&left, &right) {
                (Pnf::Forall(f), _) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &right);
                    pnf(&Fof::forall(vars, Fof::from(fmla).and(right.into())))
                }
                (Pnf::Exists(e), _) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &right);
                    pnf(&Fof::exists(vars, Fof::from(fmla).and(right.into())))
                }
                (_, Pnf::Forall(f)) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &left);
                    pnf(&Fof::forall(vars, Fof::from(left).and(fmla.into())))
                }
                (_, Pnf::Exists(e)) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &left);
                    pnf(&Fof::exists(vars, Fof::from(left).and(fmla.into())))
                }
                (Pnf::QFF(left), Pnf::QFF(right)) => And {
                    left: left.clone(),
                    right: right.clone(),
                }
                .into(),
            }
        }
        // e.g. (Q x. F(x)) | G(y) => Q x'. F(x') | G(y) or F(x) | (Q y. G(y)) => Q y'. F(x) | G(y')
        Fof::Or(this) => {
            let left = pnf(&this.left);
            let right = pnf(&this.right);

            match (&left, &right) {
                (Pnf::Forall(f), _) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &right);
                    pnf(&Fof::forall(vars, Fof::from(fmla).or(right.into())))
                }
                (Pnf::Exists(e), _) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &right);
                    pnf(&Fof::exists(vars, Fof::from(fmla).or(right.into())))
                }
                (_, Pnf::Forall(f)) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &left);
                    pnf(&Fof::forall(vars, Fof::from(left).or(fmla.into())))
                }
                (_, Pnf::Exists(e)) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &left);
                    pnf(&Fof::exists(vars, Fof::from(left).or(fmla.into())))
                }
                (Pnf::QFF(left), Pnf::QFF(right)) => Or {
                    left: left.clone(),
                    right: right.clone(),
                }
                .into(),
            }
        }
        // e.g. (Q x. F(x)) -> G(y) => Q' x'. F(x') -> G(y) or F(x) -> (Q y. G(y)) => Q' y'. F(x) -> G(y')
        Fof::Implies(this) => {
            let premise = pnf(&this.premise);
            let consequence = pnf(&this.consequence);

            match (&premise, &consequence) {
                (Pnf::Forall(f), _) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &consequence);
                    pnf(&Fof::exists(
                        vars,
                        Fof::from(fmla).implies(consequence.into()),
                    ))
                }
                (Pnf::Exists(e), _) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &consequence);
                    pnf(&Fof::forall(
                        vars,
                        Fof::from(fmla).implies(consequence.into()),
                    ))
                }
                (_, Pnf::Forall(f)) => {
                    let (vars, fmla) = binary_helper(&f.variables, &f.formula, &premise);
                    pnf(&Fof::forall(vars, Fof::from(premise).implies(fmla.into())))
                }
                (_, Pnf::Exists(e)) => {
                    let (vars, fmla) = binary_helper(&e.variables, &e.formula, &premise);
                    pnf(&Fof::exists(vars, Fof::from(premise).implies(fmla.into())))
                }
                (Pnf::QFF(premise), Pnf::QFF(consequence)) => Implies {
                    premise: premise.clone(),
                    consequence: consequence.clone(),
                }
                .into(),
            }
        }
        Fof::Iff(this) => {
            let left = &this.left;
            let right = &this.right;
            let left_to_right = left.clone().implies(right.clone());
            let right_to_left = right.clone().implies(left.clone());
            pnf(&left_to_right.and(right_to_left))
        }
        Fof::Exists(this) => Pnf::exists(this.variables.clone(), pnf(&this.formula)),
        Fof::Forall(this) => Pnf::forall(this.variables.clone(), pnf(&this.formula)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assert_debug_string, assert_eq_sorted_vecs, fof, pred,
        syntax::{
            signature::{FuncSig, PredSig, Sig},
            EQ_SYM,
        },
        term, v, v_1,
    };

    fn pnf(formula: &Fof) -> Fof {
        formula.pnf().into()
    }

    #[test]
    fn test_pnf() {
        {
            let formula: Fof = "true".parse().unwrap();
            assert_debug_string!("true", pnf(&formula));
        }
        {
            let formula: Fof = "false".parse().unwrap();
            assert_debug_string!("false", pnf(&formula));
        }
        {
            let formula: Fof = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", pnf(&formula));
        }

        {
            let formula: Fof = "x = y".parse().unwrap();
            assert_debug_string!("x = y", pnf(&formula));
        }
        {
            let formula: Fof = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("P(x) -> Q(y)", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("(P(x) -> Q(y)) & (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "? x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string!("? x. ((P(x) & ~Q(y)) | R(z))", pnf(&formula));
        }
        {
            let formula: Fof = "! x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string!("! x. ((P(x) & ~Q(y)) | R(z))", pnf(&formula));
        }
        // sanity checking:
        {
            let formula: Fof = "~? x. P(x)".parse().unwrap();
            assert_debug_string!("! x. ~P(x)", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) & Q(y))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) & Q(y))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) & Q(x))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) & Q(x))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) & Q(x, y))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) & Q(x, y))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(y) & ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) & P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(y) & ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) & P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x) & ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) & P(x`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x) & ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) & P(x`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x, y) & ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) & P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x, y) & ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) & P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) | Q(y))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) | Q(y))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) | Q(x))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) | Q(x))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) | Q(x, y))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) | Q(x, y))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(y) | ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) | P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(y) | ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) | P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x) | ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) | P(x`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x) | ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) | P(x`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x, y) | ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) | P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x, y) | ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) | P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) -> Q(y))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) -> Q(y))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) -> Q(x))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) -> Q(x))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) -> Q(x, y))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) -> Q(x, y))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(y) -> ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(y) -> ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) -> P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x) -> ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) -> P(x`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x) -> ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) -> P(x`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x, y) -> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) -> P(x`, y`))", pnf(&formula));
        }
        {
            let formula: Fof = "Q(x, y) -> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) -> P(x`, y`))", pnf(&formula));
        }

        {
            let formula: Fof = "(! x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "(? x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "(! x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string!(
                "? x`. (! x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "(? x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string!(
                "! x`. (? x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "(! x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string!(
                "? x`, y`. (! x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "(? x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string!(
                "! x`, y`. (? x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "Q(y) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "Q(y) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "Q(x) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string!(
                "! x`. (? x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "Q(x) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string!(
                "? x`. (! x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "Q(x, y) <=> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!(
                "! x`, y`. (? x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "Q(x, y) <=> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!(
                "? x`, y`. (! x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                pnf(&formula),
            );
        }
        //renaming tests
        assert_debug_string!(
            "! x``, x`. (P(x``) & Q(x))",
            pnf(
                &Fof::forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]).into())
                    .and(pred!(Q).app(vec![term!(x)]).into())
            ),
        );
        assert_debug_string!(
            "? x``, x`. (P(x``) & Q(x))",
            pnf(
                &Fof::exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]).into())
                    .and(pred!(Q).app(vec![term!(x)]).into())
            ),
        );
        assert_debug_string!(
            "? x``. (P(x``) & Q(x, x`))",
            pnf(&Fof::exists(vec![v!(x)], fof!(P(x)))
                .and(pred!(Q).app(vec![term!(x), v_1!(x).into()]).into())
                .into()),
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) & Q(x))",
            pnf(&Fof::exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]).into()
            )
            .and(fof!(Q(x)))),
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) & P(x``))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)])).and(Fof::forall(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)]).into()
            ))),
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) & P(x``))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)])).and(Fof::exists(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)]).into()
            ))),
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) & P(x``))",
            pnf(
                &Fof::from(pred!(Q).app(vec![term!(x), v_1!(x).into()])).and(Fof::exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x)]).into()
                ))
            ),
        );
        assert_debug_string!(
            "? x``. (Q(x) & P(x``, x`))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)])).and(Fof::exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]).into(),
            ))),
        );

        assert_debug_string!(
            "! x``, x`. (P(x``) | Q(x))",
            pnf(
                &Fof::forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]).into()).or(pred!(
                    Q
                )
                .app(vec![term!(x)])
                .into())
            ),
        );
        assert_debug_string!(
            "? x``, x`. (P(x``) | Q(x))",
            pnf(
                &Fof::exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]).into()).or(pred!(
                    Q
                )
                .app(vec![term!(x)])
                .into())
            )
        );
        assert_debug_string!(
            "? x``. (P(x``) | Q(x, x`))",
            pnf(
                &Fof::exists(vec![v!(x)], pred!(P).app(vec![term!(x)]).into())
                    .or(pred!(Q).app(vec![term!(x), v_1!(x).into()]).into())
            )
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) | Q(x))",
            pnf(&Fof::exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]).into()
            )
            .or(pred!(Q).app(vec![term!(x)]).into())
            .into())
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) | P(x``))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)])).or(Fof::forall(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)]).into()
            )))
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) | P(x``))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)])).or(Fof::exists(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)]).into()
            )))
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) | P(x``))",
            pnf(
                &Fof::from(pred!(Q).app(vec![term!(x), v_1!(x).into()])).or(Fof::exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x)]).into()
                ))
            )
        );
        assert_debug_string!(
            "? x``. (Q(x) | P(x``, x`))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)])).or(Fof::exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]).into(),
            )))
        );

        assert_debug_string!(
            "? x``, x`. (P(x``) -> Q(x))",
            pnf(&Fof::forall(
                vec![v!(x), v_1!(x)],
                Fof::from(pred!(P).app(vec![term!(x)]))
            )
            .implies(pred!(Q).app(vec![term!(x)]).into()))
        );
        assert_debug_string!(
            "! x``, x`. (P(x``) -> Q(x))",
            pnf(&Fof::exists(
                vec![v!(x), v_1!(x)],
                Fof::from(pred!(P).app(vec![term!(x)]))
            )
            .implies(pred!(Q).app(vec![term!(x)]).into())
            .into())
        );
        assert_debug_string!(
            "! x``. (P(x``) -> Q(x, x`))",
            pnf(
                &Fof::exists(vec![v!(x)], Fof::from(pred!(P).app(vec![term!(x)])))
                    .implies(pred!(Q).app(vec![term!(x), v_1!(x).into()]).into())
            )
        );
        assert_debug_string!(
            "! x``. (P(x``, x`) -> Q(x))",
            pnf(&Fof::exists(
                vec![v!(x)],
                Fof::from(pred!(P).app(vec![term!(x), v_1!(x).into()]))
            )
            .implies(pred!(Q).app(vec![term!(x)]).into()))
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) -> P(x``))",
            pnf(
                &Fof::from(pred!(Q).app(vec![term!(x)])).implies(Fof::forall(
                    vec![v!(x), v_1!(x)],
                    pred!(P).app(vec![term!(x)]).into()
                ))
            )
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) -> P(x``))",
            pnf(
                &Fof::from(pred!(Q).app(vec![term!(x)])).implies(Fof::exists(
                    vec![v!(x), v_1!(x)],
                    pred!(P).app(vec![term!(x)]).into()
                ))
            )
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) -> P(x``))",
            pnf(
                &Fof::from(pred!(Q).app(vec![term!(x), v_1!(x).into()])).implies(Fof::exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x)]).into()
                ))
            )
        );
        assert_debug_string!(
            "? x``. (Q(x) -> P(x``, x`))",
            pnf(
                &Fof::from(pred!(Q).app(vec![term!(x)])).implies(Fof::exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x), v_1!(x).into()]).into(),
                ))
            )
        );

        assert_debug_string!(
            "? x``, x`. (! x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            pnf(&Fof::forall(
                vec![v!(x), v_1!(x)],
                Fof::from(pred!(P).app(vec![term!(x)]))
            )
            .iff(pred!(Q).app(vec![term!(x)]).into()))
        );
        assert_debug_string!(
            "! x``, x`. (? x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            pnf(&Fof::exists(
                vec![v!(x), v_1!(x)],
                Fof::from(pred!(P).app(vec![term!(x)]))
            )
            .iff(pred!(Q).app(vec![term!(x)]).into()))
        );
        assert_debug_string!(
            "! x``. (? x```. ((P(x``) -> Q(x, x`)) & (Q(x, x`) -> P(x```))))",
            pnf(
                &Fof::exists(vec![v!(x)], Fof::from(pred!(P).app(vec![term!(x)])))
                    .iff(Fof::from(pred!(Q).app(vec![term!(x), v_1!(x).into()])))
                    .into()
            )
        );
        assert_debug_string!(
            "! x``. (? x```. ((P(x``, x`) -> Q(x)) & (Q(x) -> P(x```, x`))))",
            pnf(&Fof::exists(
                vec![v!(x)],
                Fof::from(pred!(P).app(vec![term!(x), v_1!(x).into()]))
            )
            .iff(pred!(Q).app(vec![term!(x)]).into()))
        );
        assert_debug_string!(
            "! x``, x`. (? x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)]))
                .iff(Fof::forall(
                    vec![v!(x), v_1!(x)],
                    pred!(P).app(vec![term!(x)]).into()
                ))
                .into())
        );
        assert_debug_string!(
            "? x``, x`. (! x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)])).iff(Fof::exists(
                vec![v!(x), v_1!(x)],
                pred!(P).app(vec![term!(x)]).into()
            )))
        );
        assert_debug_string!(
            "? x``. (! x```. ((Q(x, x`) -> P(x``)) & (P(x```) -> Q(x, x`))))",
            pnf(
                &Fof::from(pred!(Q).app(vec![term!(x), v_1!(x).into()])).iff(Fof::exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x)]).into()
                ))
            )
        );
        assert_debug_string!(
            "? x``. (! x```. ((Q(x) -> P(x``, x`)) & (P(x```, x`) -> Q(x))))",
            pnf(&Fof::from(pred!(Q).app(vec![term!(x)])).iff(Fof::exists(
                vec![v!(x)],
                pred!(P).app(vec![term!(x), v_1!(x).into()]).into(),
            )))
        );
        // both sides of binary formulae
        {
            let formula: Fof = "(! x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) & Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) | Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(? x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) -> Q(x`)))", pnf(&formula));
        }
        {
            let formula: Fof = "(! x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. (? x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "(! x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "? x. (? x`. (! x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "(? x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "! x. (! x`. (? x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "(? x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. (! x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                pnf(&formula),
            );
        }
        // multiple steps
        {
            let formula: Fof = "~~?x.P(x)".parse().unwrap();
            assert_debug_string!("? x. ~(~P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "~~!x.P(x)".parse().unwrap();
            assert_debug_string!("! x. ~(~P(x))", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) & ((! x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) & (Q(x`) & R(x)))", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) & ((? x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) & (Q(x`) & R(x)))", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) | ((! x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) | (Q(x`) | R(x)))", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) | ((? x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) | (Q(x`) | R(x)))", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) -> ((! x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) -> (Q(x`) -> R(x)))", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) -> ((? x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) -> (Q(x`) -> R(x)))", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) <=> ((! x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string!("? x`. (! x``. (! x```. (? x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", pnf(&formula));
        }
        {
            let formula: Fof = "P(x) <=> ((? x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string!("! x`. (? x``. (? x```. (! x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", pnf(&formula));
        }
        // random formulae
        {
            let formula: Fof = "!x . (P(x) -> ?y . (P(y) & Q(x, y)))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) -> (P(y) & Q(x, y))))", pnf(&formula));
        }
        {
            let formula: Fof = "?x . (P(x) & !y . (P(y) -> Q(x, y)))".parse().unwrap();
            assert_debug_string!("? x. (! y. (P(x) & (P(y) -> Q(x, y))))", pnf(&formula));
        }
        {
            let formula: Fof = "!x. (P(x) -> ~(!y . (P(y) -> Q(x, y))))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) -> ~(P(y) -> Q(x, y))))", pnf(&formula));
        }
        {
            let formula: Fof = "(P() | ? x. Q(x)) -> !z. R(z)".parse().unwrap();
            assert_debug_string!("! x. (! z. ((P() | Q(x)) -> R(z)))", pnf(&formula));
        }
        {
            let formula: Fof = "!x.?y.(!z.Q(x) & ~?x.R(x)) | (~Q(y) -> !w. R(y))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "! x. (? y. (! z. (! x`. (! w. ((Q(x) & ~R(x`)) | (~Q(y) -> R(y)))))))",
                pnf(&formula),
            );
        }
        {
            let formula: Fof = "!x. (!y. P(x, y) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string!("! x. (! y. (? y`. (P(x, y) -> Q(x, y`))))", pnf(&formula));
        }
        {
            let formula: Fof = "!x. ((!y. P(x, y)) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (? y`. (P(x, y) -> Q(x, y`))))", pnf(&formula));
        }
    }

    #[test]
    fn pnf_free_vars() {
        {
            let pnf = fof!('|').pnf();
            assert_eq!(Vec::<&Var>::new(), pnf.free_vars());
        }
        {
            let pnf = fof!(_ | _).pnf();
            assert_eq!(Vec::<&Var>::new(), pnf.free_vars());
        }
        {
            let pnf =
                fof!(!x . {? y . {[[P(x, y)] & [Q(w)]] -> [[(x) = (z)] | [~{R(x, z)}]]}}).pnf();
            assert_eq_sorted_vecs!(
                vec![v!(w), v!(z)].iter().collect::<Vec<_>>(),
                pnf.free_vars()
            );
        }
    }

    #[test]
    fn pnf_transform() {
        let pnf =
            fof!(!x . {? y . {[[P(f(x), y)] & [Q(w)]] -> [[(x) = (z)] | [~{R(f(x), z)}]]}}).pnf();
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
            fof!(!x . {? y . {[[P(z, y)] & [Q(w)]] -> [[(x) = (z)] | [~{R(z, z)}]]}}),
            Fof::from(pnf.transform_term(&f))
        );
    }

    #[test]
    fn pnf_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: "P".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: "Q".into(),
                arity: 1,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: EQ_SYM.into(),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: "f".into(),
                arity: 1,
            })
            .unwrap();
            sig.add_constant("c".into());

            let pnf =
                fof!(!x . {? y . {[[P(f(x), y)] & [Q(w)]] -> [[(@c) = (z)] | [~{P(f(x), z)}]]}})
                    .pnf();
            assert_eq!(sig, pnf.signature().unwrap());
        }
        {
            let pnf = fof!(!y. { [P(x, y) ] & [ ~(P(x)) ]}).pnf();
            assert!(pnf.signature().is_err());
        }
    }
}
