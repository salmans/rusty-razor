/*! Implements conversion to Conjunctive Normal Form (CNF) for formulae.*/

use super::SNF;
use crate::syntax::{symbol::Generator, Formula::*, *};

/// Is a wrapper around [`Formula`] that represents a formula in Conjunctive Normal Form (CNF).
///
/// **Hint**: A CNF is a formula that is a conjunction of zero or more clauses. A clause is a
/// disjunction of atomic formulae (including equations).
///
/// [`Formula`]: ../syntax/enum.Formula.html
#[derive(Clone, Debug)]
pub struct CNF(Formula);

impl CNF {
    /// Returns a reference to the formula wrapped in the receiver CNF.
    pub fn formula(&self) -> &Formula {
        &self.0
    }
}

impl From<CNF> for Formula {
    fn from(cnf: CNF) -> Self {
        cnf.0
    }
}

// Distributes conjunctions in the given formula. The function assumes that its input is an NNF.
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
        _ => unreachable!(), // NNF input
    }
}

// Eliminates the existential quantifiers of the input formula.
fn remove_forall(formula: Formula) -> Formula {
    if let Forall { formula, .. } = formula {
        remove_forall(*formula)
    } else {
        formula
    }
}

impl SNF {
    /// Transform the receiver SNF to a Conjunctive Normal Form (CNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
    /// let snf = formula.pnf().snf();
    /// let cnf = snf.cnf();
    /// assert_eq!("((¬P(x)) ∨ Q(y)) ∧ ((¬Q(y)) ∨ P(x))", Formula::from(cnf).to_string());
    /// ```
    pub fn cnf(&self) -> CNF {
        let nnf = Formula::from(self.clone()).nnf();
        CNF(remove_forall(distribute_or(&nnf.into())))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    fn cnf(formula: &Formula) -> Formula {
        formula.pnf().snf().cnf().into()
    }

    #[test]
    fn test_cnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string!("true", cnf(&formula));
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string!("false", cnf(&formula));
        }
        {
            let formula: Formula = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", cnf(&formula));
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", cnf(&formula));
        }
        {
            let formula: Formula = "x=y".parse().unwrap();
            assert_debug_string!("x = y", cnf(&formula));
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", cnf(&formula));
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", cnf(&formula));
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", cnf(&formula));
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("((~P(x)) | Q(y)) & ((~Q(y)) | P(x))", cnf(&formula));
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", cnf(&formula));
        }
        {
            let formula: Formula = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", cnf(&formula));
        }
        // quantifier-free formulae
        {
            let formula: Formula = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("((~P(x1)) | (~Q(y))) & ((~P(x2)) | (~Q(y)))", cnf(&formula));
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) | Q(x)) & (P(x) | (~Q(y)))", cnf(&formula));
        }
        {
            let formula: Formula = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) | R(z)) & ((~Q(y)) | R(z))", cnf(&formula));
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("((P(x) | (Q(x) | Q(y))) & (P(x) | (Q(x) | (~Q(x))))) & ((P(x) | ((~Q(y)) | Q(y))) & (P(x) | ((~Q(y)) | (~Q(x)))))",
                                cnf(&formula));
        }
        {
            let formula: Formula = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) | R(z)) & ((~Q(y)) | R(z))) & ((~R(z)) | (P(x) | Q(y)))",
                cnf(&formula),
            );
        }
        {
            let formula: Formula = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!(
                "(P(x) | (Q(x) | R(y))) & (P(x) | (Q(x) | R(z)))",
                cnf(&formula),
            );
        }
        {
            let formula: Formula = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!(
                "((P(x1) | Q(x1)) & (P(x1) | Q(x2))) & ((P(x2) | Q(x1)) & (P(x2) | Q(x2)))",
                cnf(&formula),
            );
        }
        //random formulae
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string!("P('sk#0)", cnf(&formula));
        }
        {
            let formula: Formula = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('sk#0) & Q(f(), 'sk#0)", cnf(&formula));
        }
        {
            let formula: Formula = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("((~P(y)) | (~Q(x, y))) | R(x)", cnf(&formula));
        }
        {
            let formula: Formula = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x)) | ((~Q(y)) | (~R(x, y)))", cnf(&formula));
        }
        {
            let formula: Formula = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, x)) | Q(y)) & ((~Q(x)) | Q(y))", cnf(&formula));
        }
        {
            let formula: Formula = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!(
                "((~P(y, sk#0(y))) | Q(y)) & ((~Q(sk#0(y))) | Q(y))",
                cnf(&formula),
            );
        }
        {
            let formula: Formula = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", cnf(&formula));
        }
        {
            let formula: Formula = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", cnf(&formula));
        }
        {
            let formula: Formula = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, sk#0(x))", cnf(&formula));
        }
        {
            let formula: Formula =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!("((~R(z)) | P(sk#0(z), x)) & (((~R(z)) | (~Q(u`, x`, y))) & ((~R(z)) | (~(w = f(u`)))))",
                                cnf(&formula));
        }
        {
            let formula: Formula = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(y) | Q(sk#0(x, y), x)) & ((~Q(x, y)) | Q(sk#0(x, y), x))",
                cnf(&formula),
            );
        }
        {
            let formula: Formula = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(sk#0(x)) | Q(sk#1(x), x)) & ((~Q(x, sk#0(x))) | Q(sk#1(x), x))",
                cnf(&formula),
            );
        }
        {
            let formula: Formula = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "P('sk#0) & (((~Q('sk#0, y)) | (y = z)) | (~Q('sk#0, z)))",
                cnf(&formula),
            );
        }
        {
            let formula: Formula =
                "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                    .parse()
                    .unwrap();
            assert_debug_string!("((~P(x)) | ((~P(y)) | P(f(x, y)))) & (((~P(x)) | Q(x, sk#0(x, y))) & ((~P(x)) | (~P(sk#0(x, y)))))",
                                cnf(&formula));
        }
    }
}
