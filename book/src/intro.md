# Introduction

Rusty Razor is a tool for constructing finite models for first-order theories. The model-finding algorithm is inspired
by [The Chase](https://en.wikipedia.org/wiki/Chase_(algorithm)) for database systems. Given a first-order theory,
Razor constructs a set of *homomorphically minimal* models. The constructed models are models of an equisatisfiable
theory over an alphabet, extended with Skolem functions that represent the existential quantifiers of the original theory.

To learn more about the theoretical foundation of Razor, check out my
[PhD dissertation](https://digitalcommons.wpi.edu/etd-dissertations/458/).