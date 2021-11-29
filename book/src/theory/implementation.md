## Implementation

Razor's model-finding algorithm is a variant of [the chase][chase], an
algorithm for constructing models for geometric theories. Given an
input first-order theory 𝓣, Razor applies a standard syntactic
transformation to convert 𝓣 to a *Geometric Normal Form* (GNF). The
result of this transformation is a geometric theory 𝓖 that is
equisatisfiable with 𝓣.

> **Note:** Transformation to GNF consists of transforming the input
theory to a [Conjunctive Normal Form][cnf] (CNF) followed by
rearranging the conjuncts of the resulting CNF into an implication,
where negative and positive conjuncts form the implication's premise
and consequence respectively. The implication is semantically
equivalent to a geometric sequence and is treated as such.
>
> It's noteworthy that conversion to CNF involves
[*Skolemization*][skolem], a transformation by which existential
quantifiers of the input theory are replaced with fresh "Skolem
functions". Therefore, the resulting GNF is a theory over an extension
of the original vocabulary over which the input theory is defined.

[chase]: ./theory/chase.html
[cnf]: https://en.wikipedia.org/wiki/Conjunctive_normal_form#Converting_from_first-order_logic
[skolem]: https://en.wikipedia.org/wiki/Skolem_normal_form

Let 𝓖 be an input geometric theory. The essense of a
[chase-step][step] on a model 𝕞 is to find a sequent 𝜑 ⊢<sub>𝘅</sub> 𝜓
of 𝓖 with an assignment from the variables in 𝘅 to the domain of 𝕞
such that 𝜑 is true and 𝜓 is false in 𝕞. A naive implementation of the
chase would iterate over all sequents of 𝓖 and examine every
assignment from 𝘅 to the domain of 𝕞. This would lead to |𝘅|<sup>|𝕞|</sup> valuations of 𝜑 and 𝜓 in 𝕞 where |𝘅| and |𝕞| 
denote the size of 𝘅 and the domain size of 𝕞 respectively. Such a 
naive implementation is extremely inefficient for practical 
model-finding use-cases.

A practical implementation of the chase must address a number of
algorithmic challenges: it must provide efficient data-structures for
querying models and keeping track of various search branches; it
should implement effective heuristics for choosing a search branch and
for selecting a sequent to evaluate; and most importantly, it must
implement a fast solution for finding assignments from the free
variables in 𝘅 to the elements of 𝕞.

[step]: ./theory/chase.html#step

### <a name="codd"/> Hello Codd!

[Codd's theorem][codd] is a well known result from database theory
that establishes equivalence between [relational algebra][algebra] and
[relational calculus][calculus] thus first-order logic.  Razor takes
advantage of this equivalence to implement the chase efficiently with
the help of database theory. From a database perspective, a model 𝕞
constructed by the chase can be thought of as a monotonically growing
database with relational tables for each predicate of the input theory
𝓖. Consequently, positive existential formulae are expressed queries
with conjunction (∧), disjunction (∨), and existential quantifier (∃)
acting as relational join (⋈), set union (∪), and projection (∏).
Finally, a geometric sequent 𝜑 ⊢<sub>𝘅</sub> 𝜓 is evaluated by a query
𝛷 - 𝛹, the set difference of the relational expressions corresponding
to 𝜑 and 𝜓. Intuitively, evaluating 𝛷 - 𝛹 in 𝕞 results in a set of
tuples that assign values to the variables in 𝘅 such that 𝜑 is true
and 𝜓 is false, as required by the chase-step. After evaluating 𝛷 -
𝛹, the chase-step proceeds by inserting the resulting tuples in the
relations mentioned by 𝛹, thus, making 𝜓 true in 𝕞.

Razor's implementation of the chase uses [`codd`][codd-lib], a minimal
in-memory database with relational expressions as queries. The
underlying database abstraction would enable Razor to take advantage
of many advances in database theory and particularly streaming
databases to run more efficiently.  For example, `codd` supports
incrementally updated materialized views that are used to avoid full
re-evaluation of expressions during a run of the chase as the
database (i.e., the model 𝕞) grows.

#### Relationalization

The algorithm based on relational algebra requires a relationalization
step to transform a given first-order theory 𝓣 with function symbols
to an equivalent theory 𝓣′ without functions.  Relationalization is a
standard transformation that involves flattening of complex terms
followed by replacing function symbols and constants (i.e., nullary
functions) with new predicates. This transformation also extends the
original theory with integrity axioms that preserve the semantics of
the eliminated functions.

A discussion about the details of relationalization is out of the
scope of this document. Here, I use an example to explain the core
idea. Consider the atomic formula below, where 𝚁 is a predicate, 𝚏 and
𝚐 are function symbols, 𝚡 and 𝚢 are variables, and 𝗰 is a constant:

𝚁(𝚏(𝚐(𝚡), 𝚢), 𝗰)

To flatten this formula, we introduce fresh variables, namely
𝚟<sub>1</sub>, 𝚟<sub>2</sub>, and 𝚟<sub>3</sub> to recursively replace
complex terms, consisting of function applications and
constants. Notice that the original and the flattened formulae are
semantically equivalent:

𝚁(𝚟<sub>1</sub>, 𝚟<sub>2</sub>) ∧ 𝚏(𝚟<sub>3</sub>, 𝚢) = 𝚟<sub>1</sub>
∧ 𝚐(𝚡) = 𝚟<sub>3</sub> ∧ 𝗰 = 𝚟<sub>2</sub>

Next, for each function symbol of arity 𝚗, we introduce a predicate of
arity 𝚗 + 1 and replace the equalities between function applications
and variables with atomic formulae over the new predicates:

𝚁(𝚟<sub>1</sub>, 𝚟<sub>2</sub>) ∧ 𝙵(𝚟<sub>3</sub>, 𝚢, 𝚟<sub>1</sub>) ∧
𝙶(𝚡, 𝚟<sub>3</sub>) ∧ 𝙲(𝚟<sub>2</sub>)

In the previous example, 𝙵, 𝙶, and 𝙲 replace 𝚏, 𝚐, and 𝗰 in that
order.  The last position of these predicates correspond to the output
of the functions that they replace. Finally, to preserve the semantics
of the eliminated functions, the following sequents are added to the
resulting theory 𝓣′:

𝙵(𝚡<sub>1</sub>, 𝚡<sub>2</sub>, 𝚢) ∧ 𝙵(𝚡′<sub>1</sub>, 𝚡′<sub>2</sub>,
𝚢′) ∧
𝚡<sub>1</sub> = 𝚡′<sub>1</sub> ∧ 𝚡<sub>2</sub> = 𝚡′<sub>2</sub> ⊢ 𝚢 = 𝚢′  
𝙶(𝚡, 𝚢) ∧ 𝙶(𝚡′, 𝚢′) ∧ 𝚡 = 𝚡′ ⊢ 𝚢 = 𝚢′  
𝙲(𝚢) ∧ 𝙲(𝚢′) ⊢ 𝚢 = 𝚢′

These sequents ensure that the new predicates are interpreted by
relations that map every vector of input arguments to exactly one
output, as the original functions do.

> **Note:** It's common to add another set of sequents to the
resulting relationalized theory to preserve the totality of
functions. The chase, however, interprets the functions of the input
theory as partial functions; therefore, we're not concerned with
preserving totality.

#### <a name=equality/> Equality

Interpreting equality as a relation can be done by axiomatizing
equality as a predicate, captured by the following sequents with = as
a special binary predicate symbol:

<pre> 
⊤ ⊢ =(x, x)                (reflexivity) 
=(𝚡, 𝚢) ⊢ =(𝚢, 𝚡)           (symmetry) 
=(𝚡, 𝚢) ∧ =(𝚢, 𝚣) ⊢ =(𝚡, 𝚣) (transitivity) 
</pre>

> **Note:** Our treatment of equality takes advantage of the fact that
equality axioms can be expressed as geometric sequents.

#### Variable Linearization

The translation to relational algebra must account for a number of
practical challenges regarding variables and their order of appearance
in formulae. From a database perspective, each position on the
first-order predicates represents a relational *attribute* (i.e., a
column of a relational table).  Therefore, the variables of the
formulae in the input theory enforce equality constraints on the
resulting select query. Specifically, the positions of two conjoined
predicates that are occupied by the same variable specify the *key
attributes* of a relatoinal join where equality between join
attributes is defined by the relation = from the [previous
section](#equality). As a result, Razor applies a standard
*linearization* transformation that assigns unique names to variables
that occupy positions on any predicate except for =. When renaming
variables, linearization introduces additional equalities between the
freshly introduced unique variables that rename the same variable in
the input formula.

Now, I will use another example to describe linearization:

𝙿(𝚡) ∧ 𝚀(𝚢, 𝚡, 𝚢)

A possible linearized version of the formula above is obtained by
renaming the second occurances of x and 𝚢, in 𝚀(𝚢, 𝚡, 𝚢), with new
variables, namely x<sub>0</sub> and 𝚢<sub>0</sub>. In addition, =(x,
x<sub>0</sub>) and =(𝚢, 𝚢<sub>0</sub>) are conjoined into the formula
to preserve equality between a variable and its renaming counterpart:

𝙿(𝚡) ∧ 𝚀(𝚢, 𝚡<sub>0</sub>, 𝚢<sub>0</sub>) ∧ =(x, x<sub>0</sub>) ∧ =(𝚢,
𝚢<sub>0</sub>)

#### Range Restriction

I mentioned [earlier](#codd) that in our implementation of the chase
based on relational algebra, a sequent 𝜑 ⊢<sub>𝘅</sub> 𝜓 is evaluated
as a relational expression 𝛷 - 𝛹 where 𝛷 and 𝛹 are relational
expression obtained by transforming 𝜑 and 𝜓. The set difference
operator is defined only when the attributes of 𝛷 and 𝛹 align; that
is, they must share the same attributes in the same order. If 𝛷 and 𝛹
share the same set of attributes but in different orders, it's always
possible to project either of the expressions to match the order of
attributes. If 𝛷 and 𝛹 have different attributes, two cases are
possible:

1. An attribute 𝜶 appears in 𝛷 but not in 𝛹. In this case, we simply
   project 𝜶 out of 𝛷.
1. An attribute 𝜷 appears in 𝛹 but not in 𝛷. The treatment for this
   case involves *range restriction* as described below.

In database theory, a range-restricted query



> talk about other implementations

[codd]: https://en.wikipedia.org/wiki/Codd%27s_theorem
[algebra]: https://en.wikipedia.org/wiki/Relational_algebra
[step]:./theory/chase.html#step
[calculus]: https://en.wikipedia.org/wiki/Relational_calculus
[codd-lib]: https://github.com/salmans/codd
