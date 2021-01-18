/*! Defines formulae in Negation Normal Form (NNF) and implements an algorithm for
converting a [`FOF`] to [`NNF`].

[`FOF`]: crate::syntax::FOF
*/
use crate::syntax::{
    formula::{clause::Literal, *},
    term::Complex,
    Error, Sig, Var, FOF,
};

/// Represents a formula in Negation Normal Form (NNF).
///
/// **Hint**: An NNF is a formula where negation is only applied to its atomic (including
/// equations) sub-formulae.
#[derive(Clone)]
pub enum NNF {
    /// Is logical top (⊤) or truth.    
    Top,

    /// Is logical bottom (⟘) or falsehood.    
    Bottom,

    /// Is a literal, wrapping a [`Literal`].
    Literal(Literal<Complex>),

    /// Is a conjunction of two formulae, wrapping an [`And`].    
    And(Box<And<NNF>>),

    /// Is a disjunction of two formulae, wrapping an [`Or`].
    Or(Box<Or<NNF>>),

    /// Is an existentially quantified NNF, wrapping an [`Exists`].
    Exists(Box<Exists<NNF>>),

    /// Is a universally quantified NNF, wrapping a [`Forall`].    
    Forall(Box<Forall<NNF>>),
}

impl From<Atom<Complex>> for NNF {
    fn from(value: Atom<Complex>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Equals<Complex>> for NNF {
    fn from(value: Equals<Complex>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Not<Atom<Complex>>> for NNF {
    fn from(value: Not<Atom<Complex>>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Not<Equals<Complex>>> for NNF {
    fn from(value: Not<Equals<Complex>>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<And<NNF>> for NNF {
    fn from(value: And<NNF>) -> Self {
        Self::And(value.into())
    }
}

impl From<Or<NNF>> for NNF {
    fn from(value: Or<NNF>) -> Self {
        Self::Or(value.into())
    }
}

impl From<Exists<NNF>> for NNF {
    fn from(value: Exists<NNF>) -> Self {
        Self::Exists(Box::new(value))
    }
}

impl From<Forall<NNF>> for NNF {
    fn from(value: Forall<NNF>) -> Self {
        Self::Forall(Box::new(value))
    }
}

impl From<Literal<Complex>> for NNF {
    fn from(value: Literal<Complex>) -> Self {
        Self::Literal(value)
    }
}

pub trait ToNNF: Formula {
    /// Transforms the receiver formula to a Negation Normal Form (NNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::ToNNF;
    ///
    /// let formula: FOF = "not (P(x) iff Q(y))".parse().unwrap();
    /// let nnf = formula.nnf();
    ///
    /// assert_eq!("(P(x) ∧ ¬Q(y)) ∨ (¬P(x) ∧ Q(y))", nnf.to_string());
    /// ```
    fn nnf(&self) -> NNF;
}

impl ToNNF for FOF {
    fn nnf(&self) -> NNF {
        nnf(self)
    }
}

impl<T: ToNNF> From<T> for NNF {
    fn from(value: T) -> Self {
        value.nnf()
    }
}

impl NNF {
    #[inline(always)]
    fn neg(atom: Atomic<Complex>) -> Self {
        Literal::Neg(atom).into()
    }

    #[inline(always)]
    fn and(self, formula: Self) -> Self {
        And {
            left: self,
            right: formula,
        }
        .into()
    }

    #[inline(always)]
    fn or(self, formula: Self) -> Self {
        Or {
            left: self,
            right: formula,
        }
        .into()
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

impl Formula for NNF {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        match self {
            NNF::Top => Ok(Sig::default()),
            NNF::Bottom => Ok(Sig::default()),
            NNF::Literal(this) => this.signature(),
            NNF::And(this) => this.signature(),
            NNF::Or(this) => this.signature(),
            NNF::Exists(this) => this.signature(),
            NNF::Forall(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&Var> {
        match self {
            Self::Top => Vec::new(),
            Self::Bottom => Vec::new(),
            Self::Literal(this) => this.free_vars(),
            Self::And(this) => this.free_vars(),
            Self::Or(this) => this.free_vars(),
            Self::Exists(this) => this.free_vars(),
            Self::Forall(this) => this.free_vars(),
        }
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            Self::Top => NNF::Top,
            Self::Bottom => NNF::Bottom,
            Self::Literal(this) => this.transform(f).into(),
            Self::And(this) => this.transform(f).into(),
            Self::Or(this) => this.transform(f).into(),
            Self::Exists(this) => this.transform(f).into(),
            Self::Forall(this) => this.transform(f).into(),
        }
    }
}

impl std::fmt::Display for NNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl FormulaEx for NNF {
    fn precedence(&self) -> u8 {
        match self {
            NNF::Top => PRECEDENCE_ATOM,
            NNF::Bottom => PRECEDENCE_ATOM,
            NNF::Literal(this) => this.precedence(),
            NNF::And(this) => this.precedence(),
            NNF::Or(this) => this.precedence(),
            NNF::Exists(this) => this.precedence(),
            NNF::Forall(this) => this.precedence(),
        }
    }
}

impl From<NNF> for FOF {
    fn from(value: NNF) -> Self {
        match value {
            NNF::Top => Self::Top,
            NNF::Bottom => Self::Bottom,
            NNF::Literal(lit) => match lit {
                Literal::Pos(pos) => match pos {
                    Atomic::Atom(this) => this.into(),
                    Atomic::Equals(this) => this.into(),
                },
                Literal::Neg(neg) => match neg {
                    Atomic::Atom(this) => Self::not(this.into()),
                    Atomic::Equals(this) => Self::not(this.into()),
                },
            },
            NNF::And(this) => Self::from(this.left).and(this.right.into()),
            NNF::Or(this) => Self::from(this.left).or(this.right.into()),
            NNF::Exists(this) => Self::exists(this.variables, this.formula.into()),
            NNF::Forall(this) => Self::forall(this.variables, this.formula.into()),
        }
    }
}

impl From<&NNF> for FOF {
    fn from(value: &NNF) -> Self {
        value.clone().into()
    }
}

// Recursively pushes negation in the formula.
#[inline]
fn push_not(formula: &FOF) -> NNF {
    match formula {
        FOF::Top => NNF::Bottom,
        FOF::Bottom => NNF::Top,
        FOF::Atom(this) => NNF::neg(this.clone().into()),
        FOF::Equals(this) => NNF::neg(this.clone().into()),
        FOF::Not(this) => nnf(&this.formula),
        FOF::And(this) => nnf(&FOF::not(this.left.clone())).or(nnf(&FOF::not(this.right.clone()))),
        FOF::Or(this) => nnf(&FOF::not(this.left.clone())).and(nnf(&FOF::not(this.right.clone()))),
        FOF::Implies(this) => nnf(&this.premise).and(nnf(&FOF::not(this.consequence.clone()))),
        FOF::Iff(this) => {
            let left_and_not_right = nnf(&this.left).and(nnf(&FOF::not(this.right.clone())));
            let not_left_and_right = nnf(&FOF::not(this.left.clone())).and(nnf(&this.right));
            left_and_not_right.or(not_left_and_right)
        }
        FOF::Exists(this) => {
            NNF::forall(this.variables.clone(), nnf(&FOF::not(this.formula.clone())))
        }
        FOF::Forall(this) => {
            NNF::exists(this.variables.clone(), nnf(&FOF::not(this.formula.clone())))
        }
    }
}

fn nnf(fmla: &FOF) -> NNF {
    match fmla {
        FOF::Top => NNF::Top,
        FOF::Bottom => NNF::Bottom,
        FOF::Atom(this) => this.clone().into(),
        FOF::Equals(this) => this.clone().into(),
        FOF::Not(this) => push_not(&this.formula),
        FOF::And(this) => nnf(&this.left).and(nnf(&this.right)),
        FOF::Or(this) => nnf(&this.left).or(nnf(&this.right)),
        FOF::Implies(this) => nnf(&FOF::not(this.premise.clone())).or(nnf(&this.consequence)),
        FOF::Iff(this) => {
            let not_left_or_right = nnf(&FOF::not(this.left.clone())).or(nnf(&this.right));
            let left_or_not_right = nnf(&this.left).or(nnf(&FOF::not(this.right.clone())));
            not_left_or_right.and(left_or_not_right)
        }
        FOF::Exists(this) => NNF::exists(this.variables.clone(), nnf(&this.formula)),
        FOF::Forall(this) => NNF::forall(this.variables.clone(), nnf(&this.formula)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    fn nnf(formula: &FOF) -> FOF {
        formula.nnf().into()
    }

    #[test]
    fn test_nnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_string!("true", nnf(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_string!("false", nnf(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "x = y".parse().unwrap();
            assert_debug_string!("x = y", nnf(&formula));
        }
        {
            let formula: FOF = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("~P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x) | Q(y)) & (P(x) | ~Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "?x. P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "!x. P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", nnf(&formula));
        }
        // sanity checking
        {
            let formula: FOF = "~true".parse().unwrap();
            assert_debug_string!("false", nnf(&formula));
        }
        {
            let formula: FOF = "~false".parse().unwrap();
            assert_debug_string!("true", nnf(&formula));
        }
        {
            let formula: FOF = "~~P(x)".parse().unwrap();
            assert_debug_string!("P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "~~~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "~~~~P(x)".parse().unwrap();
            assert_debug_string!("P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "~~x = y".parse().unwrap();
            assert_debug_string!("x = y", nnf(&formula));
        }
        {
            let formula: FOF = "~(P(x) & Q(y))".parse().unwrap();
            assert_debug_string!("~P(x) | ~Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~(P(x) | Q(y))".parse().unwrap();
            assert_debug_string!("~P(x) & ~Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~(P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & ~Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~(P(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) & ~Q(y)) | (~P(x) & Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("(~P(x) & ~Q(y)) | R(z)", nnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "((~P(x) & ~Q(y)) | R(z)) & ((P(x) | Q(y)) | ~R(z))",
                nnf(&formula),
            );
        }
        {
            let formula: FOF = "~?x. P(x)".parse().unwrap();
            assert_debug_string!("! x. ~P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "~!x. P(x)".parse().unwrap();
            assert_debug_string!("? x. ~P(x)", nnf(&formula));
        }
        // recursive application
        {
            let formula: FOF = "~~P(x) & ~~Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~~P(x) | ~~Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~~P(x) -> ~~Q(y)".parse().unwrap();
            assert_debug_string!("~P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~~P(x) <=> ~~Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x) | Q(y)) & (P(x) | ~Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "?x. ~~P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "!x. ~~P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "~~~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", nnf(&formula));
        }
        {
            let formula: FOF = "~(~P(x) & ~Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~(~P(x) | ~Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~(~P(x) -> ~Q(y))".parse().unwrap();
            assert_debug_string!("~P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~(~(P(x) & Q(x)) & ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(P(x) & Q(x)) | (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "~(~(P(x) & Q(x)) | ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(P(x) & Q(x)) & (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "~(~(P(x) & Q(x)) -> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(~P(x) | ~Q(x)) & (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "~(~(P(x) & Q(x)) <=> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!(
                "((~P(x) | ~Q(x)) & (P(y) & Q(y))) | ((P(x) & Q(x)) & (~P(y) | ~Q(y)))",
                nnf(&formula),
            );
        }
        {
            let formula: FOF = "~?x. !y. (P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) & ~Q(y)))", nnf(&formula));
        }
        {
            let formula: FOF = "~((?x. P(x)) & (!y. Q(y)))".parse().unwrap();
            assert_debug_string!("(! x. ~P(x)) | (? y. ~Q(y))", nnf(&formula));
        }
    }
}
