/*! Implements conversion to Conjunctive Normal Form (CNF) for formula.*/

use super::SkolemGenerator;
use crate::syntax::{Formula::*, *};

// The following distributes conjunctions in the given formula. The function assumes that
// its input is an NNF.
fn distribute_or(formula: &Formula) -> Formula {
    match formula {
        Top | Bottom | Atom { .. } | Equals { .. } | Not { .. } => formula.clone(),
        And { left, right } => distribute_or(left).and(distribute_or(right)),
        Or { left, right } => {
            let left = distribute_or(left);
            let right = distribute_or(right);
            if let And { left: l, right: r } = left {
                distribute_or(&l.or(right.clone())).and(distribute_or(&r.or(right)))
            } else if let And { left: l, right: r } = right {
                distribute_or(&left.clone().or(*l)).and(distribute_or(&left.or(*r)))
            } else {
                left.or(right)
            }
        }
        Forall { variables, formula } => forall(variables.clone(), distribute_or(formula)),
        _ => panic!("something is wrong: expecting a formula in negation normal form"),
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
    /// Returns a Conjunctive Normal Form (CNF) equivalent to the receiver.
    ///
    /// **Hint**: A CNF is a formula that is a conjunction of zero or more clauses. A clause is a
    /// disjunction of atomic formulae (including equations).
    ///
    /// **Note**: All free variables are assumed to be universally quantified.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
    /// assert_eq!("((¬P(x)) ∨ Q(y)) ∧ ((¬Q(y)) ∨ P(x))", formula.cnf().to_string());
    /// ```
    pub fn cnf(&self) -> Formula {
        self.cnf_with(&mut SkolemGenerator::new())
    }

    /// Is similar to [`Formula::cnf`] but uses an existing [`SkolemGenerator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    /// **Note**: The CNF transformation includes Skolemization.
    ///
    /// [`SkolemGenerator`]: ../transform/struct.SkolemGenerator.html
    /// [`Formula::cnf`]: ./enum.Formula.html#method.cnf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::SkolemGenerator;
    ///
    /// let mut generator = SkolemGenerator::from("s%");
    /// let formula: Formula = "exists x. ((forall y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
    /// assert_eq!("((¬P(\'s%1)) ∨ (¬Q(\'s%0, \'s%1))) ∨ R(\'s%0)",
    ///     formula.cnf_with(&mut generator).to_string());
    /// ```
    pub fn cnf_with(&self, generator: &mut SkolemGenerator) -> Formula {
        let nnf = self.snf_with(generator).nnf();
        remove_forall(distribute_or(&nnf))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    #[test]
    fn test_cnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string!("true", formula.cnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string!("false", formula.cnf());
        }
        {
            let formula: Formula = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", formula.cnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.cnf());
        }
        {
            let formula: Formula = "x=y".parse().unwrap();
            assert_debug_string!("x = y", formula.cnf());
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", formula.cnf());
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", formula.cnf());
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", formula.cnf());
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & ((~Q(y)) | P(x))", formula.cnf());
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.cnf());
        }
        {
            let formula: Formula = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", formula.cnf());
        }
        // quantifier-free formulae
        {
            let formula: Formula = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("((~P(x1)) | (~Q(y))) & ((~P(x2)) | (~Q(y)))", formula.cnf());
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) | Q(x)) & (P(x) | (~Q(y)))", formula.cnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) | R(z)) & ((~Q(y)) | R(z))", formula.cnf());
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("((P(x) | (Q(x) | Q(y))) & (P(x) | (Q(x) | (~Q(x))))) & ((P(x) | ((~Q(y)) | Q(y))) & (P(x) | ((~Q(y)) | (~Q(x)))))",
                                formula.cnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) | R(z)) & ((~Q(y)) | R(z))) & ((~R(z)) | (P(x) | Q(y)))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!(
                "(P(x) | (Q(x) | R(y))) & (P(x) | (Q(x) | R(z)))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!(
                "((P(x1) | Q(x1)) & (P(x1) | Q(x2))) & ((P(x2) | Q(x1)) & (P(x2) | Q(x2)))",
                formula.cnf(),
            );
        }
        //random formulae
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string!("P('sk#0)", formula.cnf());
        }
        {
            let formula: Formula = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('sk#0) & Q(f(), 'sk#0)", formula.cnf());
        }
        {
            let formula: Formula = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("((~P(y)) | (~Q(x, y))) | R(x)", formula.cnf());
        }
        {
            let formula: Formula = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x)) | ((~Q(y)) | (~R(x, y)))", formula.cnf());
        }
        {
            let formula: Formula = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, x)) | Q(y)) & ((~Q(x)) | Q(y))", formula.cnf());
        }
        {
            let formula: Formula = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "((~P(y, sk#0(y))) | Q(y)) & ((~Q(sk#0(y))) | Q(y))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", formula.cnf());
        }
        {
            let formula: Formula = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", formula.cnf());
        }
        {
            let formula: Formula = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, sk#0(x))", formula.cnf());
        }
        {
            let formula: Formula =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!("((~R(z)) | P(sk#0(z), x)) & (((~R(z)) | (~Q(u`, x`, y))) & ((~R(z)) | (~(w = f(u`)))))",
                                formula.cnf());
        }
        {
            let formula: Formula = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(y) | Q(sk#0(x, y), x)) & ((~Q(x, y)) | Q(sk#0(x, y), x))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(sk#0(x)) | Q(sk#1(x), x)) & ((~Q(x, sk#0(x))) | Q(sk#1(x), x))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "P('sk#0) & (((~Q('sk#0, y)) | (y = z)) | (~Q('sk#0, z)))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula =
                "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                    .parse()
                    .unwrap();
            assert_debug_string!("((~P(x)) | ((~P(y)) | P(f(x, y)))) & (((~P(x)) | Q(x, sk#0(x, y))) & ((~P(x)) | (~P(sk#0(x, y)))))",
                                formula.cnf());
        }
    }
}
