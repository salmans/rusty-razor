# Razor

[Razor] is a [first-order] model-finder. Given an input first-order theory, corresponding to the design specification of 
a system, written in Razor's [input syntax][syntax], 
Razor constructs a set of models as examples of the system's execution. The output set of models may contain examples that 
are consistent with the user's expectation and support the system's design. They may also contain surprising examples of 
unexpected behavior, which reveal potential logical flaws in the specification. Razor produces no models if the input 
theory is logically inconsistent.

==TODO: point to examples==

As a first-order model-finder, Razor is comparable to tools like [Kodkod], [MACE], and [Paradox]. Kodkod, is the underlying 
model-finding engine of [Alloy Analyzer][alloy], a modeling tool that has gained increasing recognition in the software industry, 
thanks to its intuitive language and well-crafted analysis tool. Inspired by Kodkod and Alloy, the goal of Razor is to make 
"lightweight formal methods" accessible to the general software development community, serving as a model-finding engine for 
domain specific analysis tools.

> **Note:** 
First-order *model-finding* is often confused with temporal *model-checking*, also known as *property-checking*. Both 
model-finding and model-checking are reasoning techniques that exhaustively verify properties of a system in a given search space; 
however, model-checking is the practice of verifying temporal properties in a finite-state model of the system. In contrast, 
model-finding refers to finding examples of the system's behavior by constructing models for its corresponding first-order specification.

[Razor]: https://github.com/salmans/rusty-razor
[first-order]: https://en.wikipedia.org/wiki/First-order_logic
[syntax]: https://salmans.github.io/rusty-razor/syntax.html
[Kodkod]: https://emina.github.io/kodkod/
[MACE]: https://www.mcs.anl.gov/research/projects/AR/mace
[Paradox]: http://vlsicad.eecs.umich.edu/BK/Slots/cache/www.cs.chalmers.se/~koen/paradox
[alloy]: http://alloytools.org
