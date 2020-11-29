/*! Implements conversion to Negation Normal Form (NNF) for formula.*/
use crate::syntax::{FOF::*, *};

/// Is a wrapper around [`FOF`] that represents a formula in Negation Normal Form (NNF).
///
/// **Hint**: An NNF is a formula where negation is only applied to its atomic (including
/// equations) sub-formulae.
///
/// [`FOF`]: crate::syntax::FOF
#[derive(Clone, Debug)]
pub struct NNF(FOF);

impl NNF {
    /// Returns a reference to the first-order formula wrapped in the receiver NNF.
    #[inline(always)]
    pub fn formula(&self) -> &FOF {
        &self.0
    }
}

impl From<NNF> for FOF {
    fn from(nnf: NNF) -> Self {
        nnf.0
    }
}

// Recursively pushes negation in the formula.
#[inline]
fn push_not(formula: &FOF) -> FOF {
    match formula {
        Top => Bottom,
        Bottom => Top,
        Atom { .. } | Equals { .. } => not(formula.clone()),
        Not(this) => this.formula.clone(),
        And(this) => nnf(&not(this.left.clone())).or(nnf(&not(this.right.clone()))),
        Or(this) => nnf(&not(this.left.clone())).and(nnf(&not(this.right.clone()))),
        Implies(this) => nnf(&this.premise).and(nnf(&not(this.consequence.clone()))),
        Iff(this) => {
            let left_and_not_right = nnf(&this.left).and(nnf(&not(this.right.clone())));
            let not_left_and_right = nnf(&not(this.left.clone())).and(nnf(&this.right));
            left_and_not_right.or(not_left_and_right)
        }
        Exists(this) => forall(this.variables.clone(), nnf(&not(this.formula.clone()))),
        Forall(this) => exists(this.variables.clone(), nnf(&not(this.formula.clone()))),
    }
}

fn nnf(fmla: &FOF) -> FOF {
    match fmla {
        Top | Bottom | Atom { .. } | Equals { .. } => fmla.clone(),
        Not(this) => push_not(&this.formula),
        And(this) => nnf(&this.left).and(nnf(&this.right)),
        Or(this) => nnf(&this.left).or(nnf(&this.right)),
        Implies(this) => nnf(&not(this.premise.clone())).or(nnf(&this.consequence)),
        Iff(this) => {
            let not_left_or_right = nnf(&not(this.left.clone())).or(nnf(&this.right));
            let left_or_not_right = nnf(&this.left).or(nnf(&not(this.right.clone())));
            not_left_or_right.and(left_or_not_right)
        }
        Exists(this) => exists(this.variables.clone(), nnf(&this.formula)),
        Forall(this) => forall(this.variables.clone(), nnf(&this.formula)),
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
        NNF(nnf(self))
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
