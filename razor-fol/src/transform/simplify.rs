/*! Implementas a basic syntactic simplification for formula. */
use crate::syntax::{FOF::*, *};

impl FOF {
    /// Applies a number of syntactic transformations to simplify the receiver
    /// first-order formula.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "not (not P())".parse().unwrap();
    /// assert_eq!("P()", formula.simplify().to_string());
    ///
    /// let formula: FOF = "forall x. (P() and true) | (Q(x) or false)".parse().unwrap();
    /// assert_eq!("∀ x. (P() ∨ Q(x))", formula.simplify().to_string());
    /// ```
    pub fn simplify(&self) -> FOF {
        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not(this) => {
                let formula = this.formula.simplify();
                match formula {
                    Top => Bottom,
                    Bottom => Top,
                    Not(this) => this.formula.simplify(),
                    _ => FOF::not(formula),
                }
            }
            And(this) => {
                let left = this.left.simplify();
                let right = this.right.simplify();
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
            Or(this) => {
                let left = this.left.simplify();
                let right = this.right.simplify();
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
            Implies(this) => {
                let left = this.premise.simplify();
                let right = this.consequence.simplify();
                if let Bottom = left {
                    Top
                } else if let Top = right {
                    Top
                } else if let Top = left {
                    right
                } else if let Bottom = right {
                    FOF::not(left).simplify()
                } else {
                    left.implies(right)
                }
            }
            Iff(this) => {
                let left = this.left.simplify();
                let right = this.right.simplify();
                if let Top = left {
                    right
                } else if let Top = right {
                    left
                } else if let Bottom = left {
                    FOF::not(right).simplify()
                } else if let Bottom = right {
                    FOF::not(left).simplify()
                } else {
                    left.iff(right)
                }
            }
            Exists(this) => {
                let formula = this.formula.simplify();
                let free_vars = formula.free_vars();
                let vs: Vec<V> = free_vars
                    .into_iter()
                    .filter(|v| this.variables.contains(v))
                    .cloned()
                    .collect();
                if vs.is_empty() {
                    formula
                } else {
                    FOF::exists(vs, formula)
                }
            }
            Forall(this) => {
                let formula = this.formula.simplify();
                let free_vars = formula.free_vars();
                let vs: Vec<V> = free_vars
                    .into_iter()
                    .filter(|v| this.variables.contains(v))
                    .cloned()
                    .collect();
                if vs.is_empty() {
                    formula
                } else {
                    FOF::forall(vs, formula)
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
            let formula: FOF = "~true".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "~false".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: FOF = "true & true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false & false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "false & true".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "true & false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "P(x) & true".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "false & P(x)".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "P(x) & false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "true & P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "P(x) & Q(x)".parse().unwrap();
            assert_debug_string!("P(x) & Q(x)", formula.simplify());
        }
        {
            let formula: FOF = "true | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false | false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "false | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "true | false".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "P(x) | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false | P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "P(x) | false".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "true | P(x)".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "P(x) | Q(x)".parse().unwrap();
            assert_debug_string!("P(x) | Q(x)", formula.simplify());
        }
        {
            let formula: FOF = "true -> true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false -> false".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false -> true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "true -> false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "P(x) -> true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false -> P(x)".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "P(x) -> false".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: FOF = "true -> P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "P(x) -> Q(x)".parse().unwrap();
            assert_debug_string!("P(x) -> Q(x)", formula.simplify());
        }
        {
            let formula: FOF = "true <=> true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false <=> false".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false <=> true".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "true <=> false".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
        {
            let formula: FOF = "P(x) <=> true".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "false <=> P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: FOF = "P(x) <=> false".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: FOF = "true <=> P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "P(x) <=> Q(x)".parse().unwrap();
            assert_debug_string!("P(x) <=> Q(x)", formula.simplify());
        }
        {
            let formula: FOF = "?x, y. P(y, z)".parse().unwrap();
            assert_debug_string!("? y. P(y, z)", formula.simplify());
        }
        {
            let formula: FOF = "?x. P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", formula.simplify());
        }
        {
            let formula: FOF = "?x. P(y)".parse().unwrap();
            assert_debug_string!("P(y)", formula.simplify());
        }
        {
            let formula: FOF = "!x, y. P(y, z)".parse().unwrap();
            assert_debug_string!("! y. P(y, z)", formula.simplify());
        }
        {
            let formula: FOF = "!x. P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", formula.simplify());
        }
        {
            let formula: FOF = "!x. P(y)".parse().unwrap();
            assert_debug_string!("P(y)", formula.simplify());
        }
        // random formulae
        {
            let formula: FOF = "~~P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "~~~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: FOF = "~(true -> false)".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "false | (P(x) & true)".parse().unwrap();
            assert_debug_string!("P(x)", formula.simplify());
        }
        {
            let formula: FOF = "?x. P(x) | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "?y. (P(x) -> false) & (false -> Q(x))".parse().unwrap();
            assert_debug_string!("~P(x)", formula.simplify());
        }
        {
            let formula: FOF = "!x. ?y. P(x, y) | true".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "(((x = y -> false) -> false) -> false) -> false"
                .parse()
                .unwrap();
            assert_debug_string!("x = y", formula.simplify());
        }
        {
            let formula: FOF = "!x, y, z. ?z. P(x) | w = x".parse().unwrap();
            assert_debug_string!("! x. (P(x) | (w = x))", formula.simplify());
        }
        {
            let formula: FOF = "(P(x) | false) | (P(x) | true)".parse().unwrap();
            assert_debug_string!("true", formula.simplify());
        }
        {
            let formula: FOF = "(P(x) & false) & (P(x) & true)".parse().unwrap();
            assert_debug_string!("false", formula.simplify());
        }
    }
}
