## Connective Precedence

When a formula contains two or more logical connectives, the connectives
are applied by the following precedence:

* Negation (`not`) is applied first.
* Conjunction (`and`) is applied next.
* Disjunction (`or`) is applied next.
* Existential (`exists`) and universal (`forall`) quantifiers are applied next.
* Implication (`implies`) and bi-implication (`iff`) have the lowest precedence.

For example, `P() implies not Q() and R()` is a formula consisting of
an implication where `P()` is the premise and the conjunction of `not Q()`
and `R()` is the consequence.

Consecutive connectives with equal precedence are applied from left to right.
For example, `P() <=> Q() -> R()` is a formula consisting of an implication
with `P() <=> Q()` as the premise and `R()` as the consequence.

Parentheses may be used to override the precedence of connectives.
For example, in `P() and (Q() or R())` the disjunction (`or`) is applied before
the conjunction (`and`).