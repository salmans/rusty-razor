## Connective Precedence

When a formula contains two or more logical connectives, the connectives
are applied by the following order from the highest to the lowest precedence:

* Negation (`not`) is applied first.
* Conjunction (`and`) is applied next.
* Disjunction (`or`) is applied next.
* Implication (`implies`) and bi-implication (`iff`) are applied next.
* Existential (`exists`) and universal (`forall`) quantifiers are applied last.

A connective with a higher precedence is applied before a consecutive
connective with a lower precedence; that is, the connective with the higher
precedence binds tighter to the formula on which it operates.
For example, `P() implies not Q() and R()` is a formula consisting of
an implication where `P()` is the premise and the conjunction of `not Q()`
and `R()` is the consequence.

Parentheses may be used to override the precedence of connectives.
For example, in `P() and (Q() or R())` the disjunction (`or`) is applied before
the conjunction (`and`).

### Associativity

All binary connectives of equal precedence except for implication
(`implies`) and bi-implication (`iff`) are left-associative.
For example, `P() | Q() | R()` is evaluated as `(P() | Q()) | R()`.

Implication and bi-implication are right-associative.
For example, `P() <=> Q() -> R() <=> S()` is evaluated as
`P() <=> (Q() -> (R() <=> S()))`.