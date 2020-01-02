# Syntax

The syntax and semantics of Razor's input is that of conventional
[first-order logic](https://en.wikipedia.org/wiki/First-order_logic),
also known as predicate logic.

Razor's input supports three [syntactic variations](./syntax/variations.html)
for the logical symbols and follows one of the more predominant conventions for
the [precedence](./syntax/precedence.html) of the logical connectives.
For consistency and readability purposes, we use the _alpha_ variation
everywhere in this document.

## Identifier

Lowercase and uppercase identifiers in Razor are defined by the following:

* A _lowercase_ identifier is a word starting with either a lowercase alphabetic character (`[a-z]`) or
the underscore (`_`), followed by any number of alphanumeric characters (`[a-zA-Z0-9]`) and/or the
underscore. For example, `rusty`, `_razor`, and `rusty123_RAZOR456` are lowercase identifiers.
* An _uppercase_ identifier is a word that starts with an uppercase alphabetic character (`[A-Z]`) and
is followed by any number of alphanumeric characters (`[a-zA-Z0-9]`) and/or the underscore (`_`).
For example, `Rusty`, and `RAZOR_123` are uppercase identifiers.

## Term

A _term_ in Razor's input is a conventional first-order term, inductively defined by the following:

* A __variable__ is a lowercase identifier, and it is a term on its own. For example, `v`,
`variable`, and `_var` may be used as variable symbols.
* A _composite_ term consists of a lowercase identifier as a __function__ symbol that is applied
to zero or more terms as arguments that are wrapped in parentheses. For example, `f()`, `f(a)`,
`f(g(a, b), c)`, and `func(plus(x, y))` are terms.

Razor treats _nullary_ functions (of arity zero that take no arguments)
as __constants__. An apostrophe (`'`) followed by a lowercase identifier is a syntactic sugar
for constructing a constant. For example, `'a` is a constant that is syntactically
equivalent to `a()`.

## <a name=formula>Formula</a>

A _formula_ in Razor's input is a conventional first-order formula _with equality_, inductively
defined by the following:

* An __atomic__ formula consists of an upper case identifier as a __predicate__ symbol that is
applied to zero or more terms as arguments that are wrapped in parentheses. For example, `R()`,
`R(x)`, and `R(f(x, 'a), y, 'b)` are atomic formulae.

* An __equality__ is a especial type of atomic formula, with a binary infix connective `=` that is
applied on two terms as its arguments. Razor treats an equality as identity between its arguments.
For example, `x = y`, and `f(x) = g(f(y), 'a)` are equalities.

* The result of applying the logical connectives `and`, `or`, `implies` and `iff` as infix binary
connectives to two fromulae is itself a formula. Parentheses may be used to override the conventional
[precedence](./syntax/precedence.html) of the connectives.
For example `P(x) and x = y`, `P(x) and (Q(y) or R(x))`, and `P(x, y) implies x = y and R(z)`
are formulae.

* The result of applying the logical connectives `forall` and `exists` to one or more comma (`,`)
separated _bound_ variables and a formula, as a propositional function, is itself a formula. The
list of bound variables and the propositional function are separated by a period (`.`).
For example, `exists x. P(x)`, `forall x, y . Q(x, y) or R(z)`, and
`forall x. exists y. P(x, y)` are formulae.

> __Note:__ A variable that is not bound by a universal (`forall`) or existential (`exists`) quantifier
is said to be a _free_ variable. Razor assumes all free variables to be universally
quantified over the entire formula in which they appear.
For example, `P(x) -> exists y . Q(x, y)` is assumed to be equivalent to
`forall x . (P(x) -> exists y . Q(x, y))`.

## Input

Razor's input is a first-order theory, consisting of a list of zero or more formulae, separated by
the semi-colon (`;`). The input may contain conventional C-style comments (`//` for comment lines and
`/*` and `*/` for comment blocks). Whitespaces including new lines are allowed.
See the following input for an example:

```
// equality axioms

forall x . x = x; /* Reflexitivity */
forall x, y . (x = y implies y = x); /* Symmetry */
forall x, y, z . (x = y and y = z implies x = z); /* Transitivity */
```