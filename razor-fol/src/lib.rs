/*! A library of first-order syntax with equality and of transformations on it: parsing, and the
normal forms [`NNF`], [`PNF`], [`SNF`], [`CNF`] and geometric sequents ([`GNF`]).

A formula reaches [`GNF`] by two routes, directly from [`NNF`] (removing only the existentials
whose scope is not positive, by a [`Geometrization`]) or through [`PNF`] → [`SNF`] → [`CNF`]
(Skolemizing every existential); Razor uses the direct route and [`Relational`] flattens its
sequents for the chase.

## References

- Saghafi, [*A Framework for Exploring Finite Models*](https://digitalcommons.wpi.edu/etd-dissertations/458/),
  PhD dissertation, Worcester Polytechnic Institute, 2015.
- Vickers, [*Geometric Logic in Computer Science*](https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf), in
  Theory and Formal Methods 1993, Springer, 1993.
- Dyckhoff and Negri, *Geometrisation of first-order logic*, Bull. Symbolic Logic 21(2), 2015.

[`NNF`]: crate::transform::NNF
[`PNF`]: crate::transform::PNF
[`SNF`]: crate::transform::SNF
[`CNF`]: crate::transform::CNF
[`GNF`]: crate::transform::GNF
[`Geometrization`]: crate::transform::Geometrization
[`Relational`]: crate::transform::Relational
*/
#[macro_use]
extern crate lalrpop_util;

pub mod parser;
pub mod syntax;
pub mod transform;

#[cfg(test)]
pub mod test_macros;
