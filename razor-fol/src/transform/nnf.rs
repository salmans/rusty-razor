/*! Implements conversion to Negation Normal Form (NNF) for formula.*/
use crate::syntax::{Formula::*, *};

/// Is a wrapper around [`Formula`] that represents a formula in Negation Normal Form (NNF).
///
/// **Hint**: An NNF is a formula where negation is only applied to its atomic (including
/// equations) sub-formulae.
///
/// [`Formula`]: ../syntax/enum.Formula.html
#[derive(Clone, Debug)]
pub struct NNF(Formula);

impl NNF {
    /// Returns a reference to the formula wrapped in the receiver NNF.
    pub fn formula(&self) -> &Formula {
        &self.0
    }
}

impl From<NNF> for Formula {
    fn from(nnf: NNF) -> Self {
        nnf.0
    }
}

// Recursively pushes negation in the formula.
#[inline]
fn push_not(formula: &Formula) -> Formula {
    match formula {
        Top => Bottom,
        Bottom => Top,
        Atom { .. } | Equals { .. } => not(formula.clone()),
        Not { formula } => *formula.clone(),
        And { left, right } => nnf(&not(*left.clone())).or(nnf(&not(*right.clone()))),
        Or { left, right } => nnf(&not(*left.clone())).and(nnf(&not(*right.clone()))),
        Implies { left, right } => nnf(&left).and(nnf(&not(*right.clone()))),
        Iff { left, right } => {
            let left_and_not_right = nnf(&left).and(nnf(&not(*right.clone())));
            let not_left_and_right = nnf(&not(*left.clone())).and(nnf(&right));
            left_and_not_right.or(not_left_and_right)
        }
        Exists { variables, formula } => forall(variables.clone(), nnf(&not(*formula.clone()))),
        Forall { variables, formula } => exists(variables.clone(), nnf(&not(*formula.clone()))),
    }
}

fn nnf(selfy: &Formula) -> Formula {
    match selfy {
        Top | Bottom | Atom { .. } | Equals { .. } => selfy.clone(),
        Not { formula: fmla } => push_not(fmla),
        And { left, right } => nnf(&left).and(nnf(&right)),
        Or { left, right } => nnf(&left).or(nnf(&right)),
        Implies { left, right } => nnf(&not(*left.clone())).or(nnf(&right)),
        Iff { left, right } => {
            let not_left_or_right = nnf(&not(*left.clone())).or(nnf(&right));
            let left_or_not_right = nnf(&left).or(nnf(&not(*right.clone())));
            not_left_or_right.and(left_or_not_right)
        }
        Exists { variables, formula } => exists(variables.clone(), nnf(&formula)),
        Forall { variables, formula } => forall(variables.clone(), nnf(&formula)),
    }
}

impl Formula {
    /// Transforms the receiver formula to a Negation Normal Form (NNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "not (P(x) iff Q(y))".parse().unwrap();
    /// let nnf = formula.nnf();
    ///
    /// assert_eq!("(P(x) ∧ (¬Q(y))) ∨ ((¬P(x)) ∧ Q(y))", Formula::from(nnf).to_string());
    /// ```
    pub fn nnf(&self) -> NNF {
        NNF(nnf(self))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    fn nnf(formula: &Formula) -> Formula {
        formula.nnf().into()
    }

    #[test]
    fn test_nnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string!("true", nnf(&formula));
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string!("false", nnf(&formula));
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", nnf(&formula));
        }
        {
            let formula: Formula = "x = y".parse().unwrap();
            assert_debug_string!("x = y", nnf(&formula));
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", nnf(&formula));
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", nnf(&formula));
        }
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", nnf(&formula));
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", nnf(&formula));
        }
        // sanity checking
        {
            let formula: Formula = "~true".parse().unwrap();
            assert_debug_string!("false", nnf(&formula));
        }
        {
            let formula: Formula = "~false".parse().unwrap();
            assert_debug_string!("true", nnf(&formula));
        }
        {
            let formula: Formula = "~~P(x)".parse().unwrap();
            assert_debug_string!("P(x)", nnf(&formula));
        }
        {
            let formula: Formula = "~~x = y".parse().unwrap();
            assert_debug_string!("x = y", nnf(&formula));
        }
        {
            let formula: Formula = "~(P(x) & Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x)) | (~Q(y))", nnf(&formula));
        }
        {
            let formula: Formula = "~(P(x) | Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x)) & (~Q(y))", nnf(&formula));
        }
        {
            let formula: Formula = "~(P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & (~Q(y))", nnf(&formula));
        }
        {
            let formula: Formula = "~(P(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) & (~Q(y))) | ((~P(x)) & Q(y))", nnf(&formula));
        }
        {
            let formula: Formula = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) & (~Q(y))) | R(z)", nnf(&formula));
        }
        {
            let formula: Formula = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) & (~Q(y))) | R(z)) & ((P(x) | Q(y)) | (~R(z)))",
                nnf(&formula),
            );
        }
        {
            let formula: Formula = "~?x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (~P(x))", nnf(&formula));
        }
        {
            let formula: Formula = "~!x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (~P(x))", nnf(&formula));
        }
        // recursive application
        {
            let formula: Formula = "~~P(x) & ~~Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "~~P(x) | ~~Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "~~P(x) -> ~~Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "~~P(x) <=> ~~Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", nnf(&formula));
        }
        {
            let formula: Formula = "?x. ~~P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", nnf(&formula));
        }
        {
            let formula: Formula = "!x. ~~P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", nnf(&formula));
        }
        {
            let formula: Formula = "~~~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", nnf(&formula));
        }
        {
            let formula: Formula = "~(~P(x) & ~Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "~(~P(x) | ~Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "~(~P(x) -> ~Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x)) & Q(y)", nnf(&formula));
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) & ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(P(x) & Q(x)) | (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) | ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(P(x) & Q(x)) & (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) -> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("((~P(x)) | (~Q(x))) & (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) <=> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) | (~Q(x))) & (P(y) & Q(y))) | ((P(x) & Q(x)) & ((~P(y)) | (~Q(y))))",
                nnf(&formula),
            );
        }
        {
            let formula: Formula = "~?x. !y. (P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) & (~Q(y))))", nnf(&formula));
        }
        {
            let formula: Formula = "~((?x. P(x)) & (!y. Q(y)))".parse().unwrap();
            assert_debug_string!("(! x. (~P(x))) | (? y. (~Q(y)))", nnf(&formula));
        }
    }
}
