/*! Implements conversion to Disjunctive Normal Form (DNF) for formula.*/

use super::SkolemGenerator;
use crate::syntax::{Formula::*, *};

// The following distributes disjunction in the given formula. The function assumes that
// its input is an NNF.
fn distribute_and(formula: &Formula) -> Formula {
    match formula {
        Top | Bottom | Atom { .. } | Equals { .. } | Not { .. } => formula.clone(),
        Or { left, right } => distribute_and(left).or(distribute_and(right)),
        And { left, right } => {
            let left = distribute_and(left);
            let right = distribute_and(right);
            if let Or { left: l, right: r } = left {
                distribute_and(&l.and(right.clone())).or(distribute_and(&r.and(right)))
            } else if let Or { left: l, right: r } = right {
                distribute_and(&left.clone().and(*l)).or(distribute_and(&left.and(*r)))
            } else {
                And {
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
        }
        Forall { variables, formula } => forall(variables.clone(), distribute_and(formula)),
        _ => panic!("Something is wrong: expecting a formula in negation normal form."),
    }
}

// The following eliminates the existential quantifiers of the input formula.
fn remove_forall(formula: Formula) -> Formula {
    if let Forall { formula, .. } = formula {
        remove_forall(*formula)
    } else {
        formula
    }
}

impl Formula {
    /// Returns a Disjunctive Normal Form (DNF) equivalent to the receiver.
    ///
    /// **Hint**: A DNF is a formula that is a disjunction of zero or more conjuncts. A conjunct
    /// is a conjunction of atomic formulae (including equations).
    ///
    /// **Note**: All of the free variables are assumed to be universally quantified.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "P(x) iff Q(y)".parse().unwrap();
    /// assert_eq!("(((¬P(x)) ∧ (¬Q(y))) ∨ ((¬P(x)) ∧ P(x))) ∨ ((Q(y) ∧ (¬Q(y))) ∨ (Q(y) ∧ P(x)))",
    ///     formula.dnf().to_string());
    /// ```
    pub fn dnf(&self) -> Formula {
        self.dnf_with(&mut SkolemGenerator::new())
    }

    /// Is similar to [`Formula::dnf`] but uses an existing [`SkolemGenerator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    /// **Note**: The DNF transformation includes Skolemization.
    ///
    /// [`SkolemGenerator`]: ../transform/struct.SkolemGenerator.html
    /// [`Formula::dnf`]: ./enum.Formula.html#method.dnf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::SkolemGenerator;
    ///
    /// let mut generator = SkolemGenerator::from("s%");
    /// let formula: Formula = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
    /// assert_eq!("((¬P(y, x)) ∧ (¬Q(x))) ∨ Q(y)", formula.dnf_with(&mut generator).to_string());
    /// ```
    pub fn dnf_with(&self, generator: &mut SkolemGenerator) -> Formula {
        let nnf = self.snf_with(generator).nnf();
        remove_forall(distribute_and(&nnf))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    #[test]
    fn test_dnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string!("true", formula.dnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string!("false", formula.dnf());
        }
        {
            let formula: Formula = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", formula.dnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.dnf());
        }
        {
            let formula: Formula = "x=y".parse().unwrap();
            assert_debug_string!("x = y", formula.dnf());
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) & (~Q(y))) | ((~P(x)) & P(x))) | ((Q(y) & (~Q(y))) | (Q(y) & P(x)))",
                formula.dnf(),
            );
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.dnf());
        }
        {
            let formula: Formula = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", formula.dnf());
        }
        // quantifier-free formulae
        {
            let formula: Formula = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("((~P(x1)) & (~P(x2))) | (~Q(y))", formula.dnf());
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | (Q(x) & (~Q(y)))", formula.dnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) & (~Q(y))) | R(z)", formula.dnf());
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!(
                "P(x) | ((Q(x) & (~Q(y))) | (Q(y) & (~Q(x))))",
                formula.dnf(),
            );
        }
        {
            let formula: Formula = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!("((((~P(x)) & (~Q(y))) & (~R(z))) | ((((~P(x)) & (~Q(y))) & P(x)) | (((~P(x)) & (~Q(y))) & Q(y)))) | ((R(z) & (~R(z))) | ((R(z) & P(x)) | (R(z) & Q(y))))",
                                formula.dnf());
        }
        {
            let formula: Formula = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!("P(x) | (Q(x) | (R(y) & R(z)))", formula.dnf());
        }
        {
            let formula: Formula = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!("(P(x1) & P(x2)) | (Q(x1) & Q(x2))", formula.dnf());
        }

        //random formulae
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string!("P('sk#0)", formula.dnf());
        }
        {
            let formula: Formula = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('sk#0) & Q(f(), 'sk#0)", formula.dnf());
        }
        {
            let formula: Formula = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("((~P(y)) | (~Q(x, y))) | R(x)", formula.dnf());
        }
        {
            let formula: Formula = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x)) | ((~Q(y)) | (~R(x, y)))", formula.dnf());
        }
        {
            let formula: Formula = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, x)) & (~Q(x))) | Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, sk#0(y))) & (~Q(sk#0(y)))) | Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", formula.dnf());
        }
        {
            let formula: Formula = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", formula.dnf());
        }
        {
            let formula: Formula = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, sk#0(x))", formula.dnf());
        }
        {
            let formula: Formula =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
                "(~R(z)) | (P(sk#0(z), x) & ((~Q(u`, x`, y)) & (~(w = f(u`)))))",
                formula.dnf(),
            );
        }
        {
            let formula: Formula = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!("(P(y) & (~Q(x, y))) | Q(sk#0(x, y), x)", formula.dnf());
        }
        {
            let formula: Formula = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(sk#0(x)) & (~Q(x, sk#0(x)))) | Q(sk#1(x), x)",
                formula.dnf(),
            );
        }
        {
            let formula: Formula = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!("((P('sk#0) & (~Q('sk#0, y))) | (P('sk#0) & (y = z))) | (P('sk#0) & (~Q('sk#0, z)))",
                                formula.dnf());
        }
        {
            let formula: Formula =
                "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                    .parse()
                    .unwrap();
            assert_debug_string!("(~P(x)) | (((~P(y)) & (Q(x, sk#0(x, y)) & (~P(sk#0(x, y))))) | (P(f(x, y)) & (Q(x, sk#0(x, y)) & (~P(sk#0(x, y))))))",
                                formula.dnf());
        }
    }
}
