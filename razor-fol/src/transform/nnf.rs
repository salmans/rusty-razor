/*! Defines formulae in Negation Normal Form (NNF) and implements an algorithm for
converting a [`FOF`] to [`NNF`].

[`FOF`]: crate::syntax::FOF
*/
use super::TermBased;
use crate::syntax::{formula::*, Term, FOF, V};

/// Represents a formula in Negation Normal Form (NNF).
///
/// **Hint**: An NNF is a formula where negation is only applied to its atomic (including
/// equations) sub-formulae.
#[derive(Clone, Debug)]
pub enum NNF {
    /// Is logical top (⊤) or truth.    
    Top,

    /// Is logical bottom (⟘) or falsehood.    
    Bottom,

    /// Is a literal, wrapping a [`Literal`].
    Literal(Literal),

    /// Is a conjunction of two formulae, wrapping an [`And`].    
    And(Box<And<NNF>>),

    /// Is a disjunction of two formulae, wrapping an [`Or`].
    Or(Box<Or<NNF>>),

    /// Is an existentially quantified NNF, wrapping an [`Exists`].
    Exists(Box<Exists<NNF>>),

    /// Is a universally quantified NNF, wrapping a [`Forall`].    
    Forall(Box<Forall<NNF>>),
}

impl From<Atom> for NNF {
    fn from(value: Atom) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Equals> for NNF {
    fn from(value: Equals) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Not<Atom>> for NNF {
    fn from(value: Not<Atom>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Not<Equals>> for NNF {
    fn from(value: Not<Equals>) -> Self {
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

impl From<Literal> for NNF {
    fn from(value: Literal) -> Self {
        Self::Literal(value)
    }
}

impl From<&FOF> for NNF {
    fn from(value: &FOF) -> Self {
        nnf(value)
    }
}

impl NNF {
    #[inline(always)]
    fn neg(atom: Atom) -> Self {
        Literal::Neg(atom).into()
    }

    #[inline(always)]
    fn neq(equality: Equals) -> Self {
        Literal::Neq(equality).into()
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
    fn exists(variables: Vec<V>, formula: Self) -> Self {
        Exists { variables, formula }.into()
    }

    #[inline(always)]
    fn forall(variables: Vec<V>, formula: Self) -> Self {
        Forall { variables, formula }.into()
    }
}

impl Formula for NNF {
    fn free_vars(&self) -> Vec<&V> {
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
}

impl TermBased for NNF {
    #[inline]
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
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

impl From<NNF> for FOF {
    fn from(value: NNF) -> Self {
        match value {
            NNF::Top => Self::Top,
            NNF::Bottom => Self::Bottom,
            NNF::Literal(lit) => match lit {
                Literal::Atom(this) => this.into(),
                Literal::Neg(this) => Self::not(this.into()),
                Literal::Equals(this) => this.into(),
                Literal::Neq(this) => Self::not(this.into()),
            },
            NNF::And(this) => Self::from(this.left).and(this.right.into()),
            NNF::Or(this) => Self::from(this.left).or(this.right.into()),
            NNF::Exists(this) => Self::exists(this.variables, this.formula.into()),
            NNF::Forall(this) => Self::forall(this.variables, this.formula.into()),
        }
    }
}

// Recursively pushes negation in the formula.
#[inline]
fn push_not(formula: &FOF) -> NNF {
    match formula {
        FOF::Top => NNF::Bottom,
        FOF::Bottom => NNF::Top,
        FOF::Atom(this) => NNF::neg(this.clone()),
        FOF::Equals(this) => NNF::neq(this.clone()),
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

impl FOF {
    /// Transforms the receiver first-order formula to a Negation Normal Form (NNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "not (P(x) iff Q(y))".parse().unwrap();
    /// let nnf = formula.nnf();
    ///
    /// assert_eq!("(P(x) ∧ (¬Q(y))) ∨ ((¬P(x)) ∧ Q(y))", FOF::from(nnf).to_string());
    /// ```
    pub fn nnf(&self) -> NNF {
        self.into()
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
            assert_debug_string!("(~P(x)) | Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", nnf(&formula));
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
            assert_debug_string!("(~P(x)) | (~Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "~(P(x) | Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x)) & (~Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "~(P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & (~Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "~(P(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) & (~Q(y))) | ((~P(x)) & Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) & (~Q(y))) | R(z)", nnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) & (~Q(y))) | R(z)) & ((P(x) | Q(y)) | (~R(z)))",
                nnf(&formula),
            );
        }
        {
            let formula: FOF = "~?x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (~P(x))", nnf(&formula));
        }
        {
            let formula: FOF = "~!x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (~P(x))", nnf(&formula));
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
            assert_debug_string!("(~P(x)) | Q(y)", nnf(&formula));
        }
        {
            let formula: FOF = "~~P(x) <=> ~~Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", nnf(&formula));
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
            assert_debug_string!("(~P(x)) & Q(y)", nnf(&formula));
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
            assert_debug_string!("((~P(x)) | (~Q(x))) & (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: FOF = "~(~(P(x) & Q(x)) <=> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) | (~Q(x))) & (P(y) & Q(y))) | ((P(x) & Q(x)) & ((~P(y)) | (~Q(y))))",
                nnf(&formula),
            );
        }
        {
            let formula: FOF = "~?x. !y. (P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) & (~Q(y))))", nnf(&formula));
        }
        {
            let formula: FOF = "~((?x. P(x)) & (!y. Q(y)))".parse().unwrap();
            assert_debug_string!("(! x. (~P(x))) | (? y. (~Q(y)))", nnf(&formula));
        }
    }
}
