/*! Implements conversion to Negation Normal Form (NNF) for formula.*/

use crate::syntax::{Formula::*, *};

impl Formula {
    /// Returns an Negation Normal Form (NNF) equivalent to the receiver.
    ///
    /// **Hint**: An NNF is a formula where negation is only applied to its atomic (including
    /// equations) sub-formulae.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "not (P(x) iff Q(y))".parse().unwrap();
    /// assert_eq!("(P(x) ∧ (¬Q(y))) ∨ ((¬P(x)) ∧ Q(y))", formula.nnf().to_string());
    /// ```
    pub fn nnf(&self) -> Formula {
        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not { ref formula } => match **formula {
                Top => Bottom,
                Bottom => Top,
                Atom { .. } | Equals { .. } => self.clone(),
                Not { ref formula } => *formula.clone(),
                And {
                    ref left,
                    ref right,
                } => not(*left.clone()).nnf().or(not(*right.clone()).nnf()),
                Or {
                    ref left,
                    ref right,
                } => not(*left.clone()).nnf().and(not(*right.clone()).nnf()),
                Implies {
                    ref left,
                    ref right,
                } => left.nnf().and(not(*right.clone()).nnf()),
                Iff {
                    ref left,
                    ref right,
                } => left
                    .nnf()
                    .and(not(*right.clone()).nnf())
                    .or(not(*left.clone()).nnf().and(right.nnf())),
                Exists {
                    ref variables,
                    ref formula,
                } => forall(variables.clone(), not(*formula.clone()).nnf()),
                Forall {
                    ref variables,
                    ref formula,
                } => exists(variables.clone(), not(*formula.clone()).nnf()),
            },
            And { left, right } => left.nnf().and(right.nnf()),
            Or { left, right } => left.nnf().or(right.nnf()),
            Implies { left, right } => not(*left.clone()).nnf().or(right.nnf()),
            Iff { left, right } => not(*left.clone())
                .nnf()
                .or(right.nnf())
                .and(left.nnf().or(not(*right.clone()).nnf())),
            Exists { variables, formula } => exists(variables.clone(), formula.nnf()),
            Forall { variables, formula } => forall(variables.clone(), formula.nnf()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    #[test]
    fn test_nnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string!("true", formula.nnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string!("false", formula.nnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.nnf());
        }
        {
            let formula: Formula = "x = y".parse().unwrap();
            assert_debug_string!("x = y", formula.nnf());
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.nnf());
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", formula.nnf());
        }
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", formula.nnf());
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", formula.nnf());
        }
        // sanity checking
        {
            let formula: Formula = "~true".parse().unwrap();
            assert_debug_string!("false", formula.nnf());
        }
        {
            let formula: Formula = "~false".parse().unwrap();
            assert_debug_string!("true", formula.nnf());
        }
        {
            let formula: Formula = "~~P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.nnf());
        }
        {
            let formula: Formula = "~~x = y".parse().unwrap();
            assert_debug_string!("x = y", formula.nnf());
        }
        {
            let formula: Formula = "~(P(x) & Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x)) | (~Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(P(x) | Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x)) & (~Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & (~Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(P(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) & (~Q(y))) | ((~P(x)) & Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) & (~Q(y))) | R(z)", formula.nnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) & (~Q(y))) | R(z)) & ((P(x) | Q(y)) | (~R(z)))",
                formula.nnf(),
            );
        }
        {
            let formula: Formula = "~?x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (~P(x))", formula.nnf());
        }
        {
            let formula: Formula = "~!x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (~P(x))", formula.nnf());
        }
        // recursive application
        {
            let formula: Formula = "~~P(x) & ~~Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~~P(x) | ~~Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~~P(x) -> ~~Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~~P(x) <=> ~~Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", formula.nnf());
        }
        {
            let formula: Formula = "?x. ~~P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", formula.nnf());
        }
        {
            let formula: Formula = "!x. ~~P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", formula.nnf());
        }
        {
            let formula: Formula = "~~~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.nnf());
        }
        {
            let formula: Formula = "~(~P(x) & ~Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~(~P(x) | ~Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~(~P(x) -> ~Q(y))".parse().unwrap();
            assert_debug_string!("(~P(x)) & Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) & ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(P(x) & Q(x)) | (P(y) & Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) | ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(P(x) & Q(x)) & (P(y) & Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) -> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("((~P(x)) | (~Q(x))) & (P(y) & Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) <=> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) | (~Q(x))) & (P(y) & Q(y))) | ((P(x) & Q(x)) & ((~P(y)) | (~Q(y))))",
                formula.nnf(),
            );
        }
        {
            let formula: Formula = "~?x. !y. (P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) & (~Q(y))))", formula.nnf());
        }
        {
            let formula: Formula = "~((?x. P(x)) & (!y. Q(y)))".parse().unwrap();
            assert_debug_string!("(! x. (~P(x))) | (? y. (~Q(y)))", formula.nnf());
        }
    }
}
