/*! Implements conversion to Disjunctive Normal Form (DNF) for formulae.*/

use super::SNF;
use crate::syntax::{FOF::*, *};

/// Is a wrapper around [`FOF`] that represents a formula in Disjunctive Normal Form (DNF).
///
/// **Hint**: A DNF is a first-order formula that is a disjunction of zero or more
/// conjuncts. A conjunct is a conjunction of atomic formulae (including equations).
///
/// [`FOF`]: crate::syntax::FOF
#[derive(Clone, Debug)]
pub struct DNF(FOF);

impl DNF {
    /// Returns a reference to the first-order formula wrapped in the receiver DNF.
    #[inline(always)]
    pub fn formula(&self) -> &FOF {
        &self.0
    }
}

impl From<DNF> for FOF {
    fn from(dnf: DNF) -> Self {
        dnf.0
    }
}

// Distributes disjunction in the given formula. The function assumes that its input is an NNF.
fn distribute_and(formula: &FOF) -> FOF {
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
                left.and(right)
            }
        }
        Forall { variables, formula } => forall(variables.clone(), distribute_and(formula)),
        _ => unreachable!(), // NNF input
    }
}

// Eliminates the existential quantifiers of the input formula.
fn remove_forall(formula: FOF) -> FOF {
    if let Forall { formula, .. } = formula {
        remove_forall(*formula)
    } else {
        formula
    }
}

impl SNF {
    /// Transform the receiver SNF to a Disjunctive Normal Form (DNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "P(x) iff Q(y)".parse().unwrap();
    /// let snf = formula.pnf().snf();
    /// let dnf = snf.dnf();
    ///
    /// assert_eq!(
    ///    "(((¬P(x)) ∧ (¬Q(y))) ∨ ((¬P(x)) ∧ P(x))) ∨ ((Q(y) ∧ (¬Q(y))) ∨ (Q(y) ∧ P(x)))",
    ///    FOF::from(dnf).to_string()
    /// );
    /// ```
    pub fn dnf(&self) -> DNF {
        let nnf = self.formula().nnf();
        DNF(remove_forall(distribute_and(&nnf.into())))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assert_debug_string;

    fn dnf(formula: &FOF) -> FOF {
        formula.pnf().snf().dnf().into()
    }

    #[test]
    fn test_dnf() {
        {
            let formula: FOF = "true".parse().unwrap();
            assert_debug_string!("true", dnf(&formula));
        }
        {
            let formula: FOF = "false".parse().unwrap();
            assert_debug_string!("false", dnf(&formula));
        }
        {
            let formula: FOF = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), f()))", dnf(&formula));
        }
        {
            let formula: FOF = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", dnf(&formula));
        }
        {
            let formula: FOF = "x=y".parse().unwrap();
            assert_debug_string!("x = y", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x)) | Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "(((~P(x)) & (~Q(y))) | ((~P(x)) & P(x))) | ((Q(y) & (~Q(y))) | (Q(y) & P(x)))",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. P(x)".parse().unwrap();
            assert_debug_string!("P(x)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string!("P(f(), g(f(), x))", dnf(&formula));
        }
        // quantifier-free formulae
        {
            let formula: FOF = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string!("((~P(x1)) & (~P(x2))) | (~Q(y))", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | (Q(x) & (~Q(y)))", dnf(&formula));
        }
        {
            let formula: FOF = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("((~P(x)) & (~Q(y))) | R(z)", dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!(
                "P(x) | ((Q(x) & (~Q(y))) | (Q(y) & (~Q(x))))",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!("((((~P(x)) & (~Q(y))) & (~R(z))) | ((((~P(x)) & (~Q(y))) & P(x)) | (((~P(x)) & (~Q(y))) & Q(y)))) | ((R(z) & (~R(z))) | ((R(z) & P(x)) | (R(z) & Q(y))))",
                                dnf(&formula));
        }
        {
            let formula: FOF = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string!("P(x) | (Q(x) | (R(y) & R(z)))", dnf(&formula));
        }
        {
            let formula: FOF = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string!("(P(x1) & P(x2)) | (Q(x1) & Q(x2))", dnf(&formula));
        }

        //random formulae
        {
            let formula: FOF = "?x. P(x)".parse().unwrap();
            assert_debug_string!("P('sk#0)", dnf(&formula));
        }
        {
            let formula: FOF = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string!("P('sk#0) & Q(f(), 'sk#0)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string!("((~P(y)) | (~Q(x, y))) | R(x)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string!("(~P(x)) | ((~Q(y)) | (~R(x, y)))", dnf(&formula));
        }
        {
            let formula: FOF = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, x)) & (~Q(x))) | Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string!("((~P(y, sk#0(y))) & (~Q(sk#0(y)))) | Q(y)", dnf(&formula));
        }
        {
            let formula: FOF = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", dnf(&formula));
        }
        {
            let formula: FOF = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("P('sk#0, 'sk#1)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string!("P(x, sk#0(x))", dnf(&formula));
        }
        {
            let formula: FOF =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string!(
                "(~R(z)) | (P(sk#0(z), x) & ((~Q(u`, x`, y)) & (~(w = f(u`)))))",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!("(P(y) & (~Q(x, y))) | Q(sk#0(x, y), x)", dnf(&formula));
        }
        {
            let formula: FOF = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "(P(sk#0(x)) & (~Q(x, sk#0(x)))) | Q(sk#1(x), x)",
                dnf(&formula),
            );
        }
        {
            let formula: FOF = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string!("((P('sk#0) & (~Q('sk#0, y))) | (P('sk#0) & (y = z))) | (P('sk#0) & (~Q('sk#0, z)))",
                                dnf(&formula));
        }
        {
            let formula: FOF = "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                .parse()
                .unwrap();
            assert_debug_string!("(~P(x)) | (((~P(y)) & (Q(x, sk#0(x, y)) & (~P(sk#0(x, y))))) | (P(f(x, y)) & (Q(x, sk#0(x, y)) & (~P(sk#0(x, y))))))",
                                dnf(&formula));
        }
    }
}
