# Geometric Logic

Razor implements a variant of [the chase][chase] algorithm to construct models for theories in 
[geometric logic][geometric], a syntactic variation of first-order logic. Geometric theories 
are comprised of geometric *sequents* in the following form:

<pre>
𝙰<sub>1</sub> ∧ ... ∧ 𝙰<sub>m</sub> ⊢<sub>𝘅</sub> (∃ 𝚢<sub>11</sub>, ..., 𝚢<sub>1j<sub>1</sub></sub> . 𝙰<sub>11</sub> ∧ ... ∧ 𝙰<sub>1n<sub>1</sub></sub>)  
              ∨ (∃ 𝚢<sub>21</sub>, ..., 𝚢<sub>2j<sub>2</sub></sub> . 𝙰<sub>21</sub> ∧ ... ∧ 𝙰<sub>2n<sub>2</sub></sub>)  
              ∨ ...  
              ∨ (∃ 𝚢<sub>i1</sub>, ..., 𝚢<sub>ij<sub>i</sub></sub> . 𝙰<sub>i1</sub> ∧ ... ∧ 𝙰<sub>in<sub>i</sub></sub>)
</pre>

where ⊢ denotes logical entailment, 𝙰<sub>k</sub>s are atomic formulae (including equality),
and 𝘅 is the set of free variables (assumed to be universally quantified) in the sequent. The premise 
(left side) and the consequence (right side) of ⊢ are respectively said to be the *body* and the *head* of 
the sequent. A body of empty conjunctions (m = 0) and a head of empty disjunctions (i = 0) are equivalent to
truth (⊤) and falsehood (⟘) respectively.

[chase]: ./theory/chase.html
[geometric]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf

### Satisfiability

It turns out that a first-order theory 𝓣 can be transformed to a geometric theory 𝓖 that is
[*equisatisfiable*] to 𝓣 via standard syntactic manipulation. That is, 𝓣 is satisfiable 
(i.e., has a model) if and only if 𝓖 is satisfiable. But 𝓖 has other desirable properties that
goes beyond equisatisfiability with 𝓣: in fact, for every model 𝕟 of 𝓣, a model 𝕞 of 𝓖 exists 
such that there is a homomorphism from 𝕞 to 𝕟. This is an important result that enables Razor 
to apply the chase to construct homomorphically [minimal] models of 𝓣.

In the context of a model-finding application, the chase constructs special models that contain
minimum amount of information required for satisfying the input theory. Equisatisfiability of 
geometric and first-order logic also implies that satisfiability of geometirc theories is 
undecidable (see [Gödel's incompleteness theorems][godel]).

> **Note:** Chapter 4 of my doctoral [dissertation] presents a comprehensive discussion about 
geometric logic and the chase.

[godel]: https://en.wikipedia.org/wiki/Gödel%27s_incompleteness_theorems
[minimal]: ./razor.html#minimality
[dissertation]: https://digital.wpi.edu/concern/etds/5q47rn87k
[*equisatisfiable*]: https://en.wikipedia.org/wiki/Equisatisfiability
