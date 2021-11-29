# Introduction

Rusty Razor is a tool for constructing finite models for first-order theories. The model-finding algorithm 
is inspired by [chase] for database systems. Given a first-order theory, Razor constructs a set of 
*homomorphically minimal* models. The constructed models are models of an equisatisfiable theory over an 
alphabet, extended with Skolem functions that represent the existential quantifiers of the original theory.

For a comprehensive theoretical discussion of Razor's approach to model-finding, see
[A Framework for Exploring Finite Models][dissertation].

[chase]: https://en.wikipedia.org/wiki/Chase_(algorithm)
[dissertation]: https://digitalcommons.wpi.edu/etd-dissertations/458/
