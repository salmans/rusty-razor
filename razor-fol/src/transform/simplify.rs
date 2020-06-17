/*! Implementas a basic syntactic simplification for formula. */

use crate::syntax::{Formula::*, *};

impl Formula {
    /// Applies a number of syntactic transformations to simplify the receiver formula.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "not (not P())".parse().unwrap();
    /// assert_eq!("P()", formula.simplify().to_string());
    ///
    /// let formula: Formula = "forall x. (P() and true) | (Q(x) or false)".parse().unwrap();
    /// assert_eq!("∀ x. (P() ∨ Q(x))", formula.simplify().to_string());
    /// ```
    pub fn simplify(&self) -> Formula {
        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not { formula } => {
                let formula = formula.simplify();
                match formula {
                    Top => Bottom,
                    Bottom => Top,
                    Not { formula } => formula.simplify(),
                    _ => not(formula),
                }
            }
            And { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Bottom = left {
                    Bottom
                } else if let Bottom = right {
                    Bottom
                } else if let Top = left {
                    right
                } else if let Top = right {
                    left
                } else {
                    left.and(right)
                }
            }
            Or { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Top = left {
                    Top
                } else if let Top = right {
                    Top
                } else if let Bottom = left {
                    right
                } else if let Bottom = right {
                    left
                } else {
                    left.or(right)
                }
            }
            Implies { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Bottom = left {
                    Top
                } else if let Top = right {
                    Top
                } else if let Top = left {
                    right
                } else if let Bottom = right {
                    not(left).simplify()
                } else {
                    left.implies(right)
                }
            }
            Iff { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Top = left {
                    right
                } else if let Top = right {
                    left
                } else if let Bottom = left {
                    not(right).simplify()
                } else if let Bottom = right {
                    not(left).simplify()
                } else {
                    left.iff(right)
                }
            }
            Exists { variables, formula } => {
                let formula = formula.simplify();
                let free_vars = formula.free_vars();
                let vs: Vec<V> = free_vars
                    .iter()
                    .filter(|v| variables.contains(v))
                    .map(|v| (*v).clone())
                    .collect();
                if vs.is_empty() {
                    formula
                } else {
                    exists(vs, formula)
                }
            }
            Forall { variables, formula } => {
                let formula = formula.simplify();
                let free_vars = formula.free_vars();
                let vs: Vec<V> = free_vars
                    .iter()
                    .filter(|v| variables.contains(v))
                    .map(|v| (*v).clone())
                    .collect();
                if vs.is_empty() {
                    formula
                } else {
                    forall(vs, formula)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    #[test]
    fn test_simplify() {
        {
            let formula: Formula = "~true".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "~false".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "true & true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false & false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "false & true".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "true & false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "P(x) & true".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "false & P(x)".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "P(x) & false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "true & P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) & Q(x)".parse().unwrap();
            assert_debug_string!("P(x) & Q(x)", formula.simplify());
        }
        {
            let formula: Formula = "true | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false | false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "false | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "true | false".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "P(x) | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false | P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) | false".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "true | P(x)".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "P(x) | Q(x)".parse().unwrap();
            assert_debug_string!("P(x) | Q(x)", formula.simplify());
        }
        {
            let formula: Formula = "true -> true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false -> false".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false -> true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "true -> false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "P(x) -> true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false -> P(x)".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "P(x) -> false".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "true -> P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) -> Q(x)".parse().unwrap();
            assert_debug_string!("P(x) -> Q(x)", formula.simplify());
        }
        {
            let formula: Formula = "true <=> true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false <=> false".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false <=> true".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "true <=> false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: Formula = "P(x) <=> true".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "false <=> P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) <=> false".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "true <=> P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) <=> Q(x)".parse().unwrap();
            assert_debug_string!("P(x) <=> Q(x)", formula.simplify());
        }
        {
            let formula: Formula = "?x, y. P(y, z)".parse().unwrap();
            assert_debug_string!("? y. P(y, z)", formula.simplify());
        }
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", formula.simplify());
        }
        {
            let formula: Formula = "?x. P(y)".parse().unwrap();
            assert_debug_string!("P(y)", formula.simplify());
        }
        {
            let formula: Formula = "!x, y. P(y, z)".parse().unwrap();
            assert_debug_string!("! y. P(y, z)", formula.simplify());
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", formula.simplify());
        }
        {
            let formula: Formula = "!x. P(y)".parse().unwrap();
            assert_debug_string!("P(y)", formula.simplify());
        }
        // random formulae
        {
            let formula: Formula = "~~P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "~~~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "~(true -> false)".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "false | (P(x) & true)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "?x. P(x) | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "?y. (P(x) -> false) & (false -> Q(x))".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "!x. ?y. P(x, y) | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "(((x = y -> false) -> false) -> false) -> false"
                .parse()
                .unwrap();
            assert_debug_string!("x = y", formula.simplify());
        }
        {
            let formula: Formula = "!x, y, z. ?z. P(x) | w = x".parse().unwrap();
            assert_debug_string!("! x. (P(x) | (w = x))", formula.simplify());
        }
        {
            let formula: Formula = "(P(x) | false) | (P(x) | true)".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: Formula = "(P(x) & false) & (P(x) & true)".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
    }
}
