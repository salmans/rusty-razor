# Background

Razor implements a variant of [the chase][chase] algorithm to construct models for first-order theories with equality. The chase operates on [geometric theories][geometric], theories that contain a syntactic
variation of first-order formulae which we refer to as the __Geometric Normal Form__ (GNF). Formulae
in GNF have the following shape:

A<sub>1</sub> ∧ ... ∧ A<sub>m</sub> →
(∃ x<sub>11</sub>, ..., x<sub>1j<sub>1</sub></sub> . A<sub>11</sub> ∧ ... ∧ A<sub>1n<sub>1</sub></sub>) </br>
&nbsp;&nbsp;&nbsp;
∨ (∃ x<sub>21</sub>, ..., x<sub>2j<sub>2</sub></sub> . A<sub>21</sub> ∧ ... ∧ A<sub>2n<sub>2</sub></sub>) </br>
&nbsp;&nbsp;&nbsp;
∨ ... </br>
&nbsp;&nbsp;&nbsp;
∨ (∃ x<sub>i1</sub>, ..., x<sub>ij<sub>i</sub></sub> . A<sub>i1</sub> ∧ ... ∧ A<sub>in<sub>i</sub></sub>)

where A<sub>k</sub>s are (positive) atomic formulae (possibly including equality) and free
variables are assumed to be universally qualified over the entire formula.

In the context of a run of the chase, we refer to the formulae in their GNF as
__sequents__. The premise (left side) and the consequence (right side) of the implication are
respectively said to be the _body_ and the _head_ of the sequent.

[chase]: https://en.wikipedia.org/wiki/Chase_(algorithm)
[geometric]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
