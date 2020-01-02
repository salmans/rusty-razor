## Satisfiability of Geometric Theories

It turns out that every first-order theory can be transformed to a geometric theory that is
_equisatisfiable_ to the original theory via standard syntactic manipulation.
In fact, for every model `N` of the original theory, there exists a model `M` of the geometric
theory such that there is a homomorphism from `M` to `N`. This is an important result that
enables Razor to utilize The Chase to construct homomorphically minimal models of a given
first-order theory.

In the context of a model-finding application, the models that The Chase produces are desirable
since they contain minimum amount of information, thus they induce minimal distraction.
As a direct consequence of semi-decidability of satisfiability in first-order logic
(see [Gödel's incompleteness theorems][godel]), satisfiability of geometric theories is
semi-decidable as well.

> __Note:__ A comprehensive discussion on the properties of the models that are constructed by
The Chase is out of the scope of this document.

[godel]: https://en.wikipedia.org/wiki/Gödel%27s_incompleteness_theorems