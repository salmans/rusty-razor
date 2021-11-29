## The Chase

The [chase] is a well-known algorithm in database theory that constructs models for geometric theories.
Given a geometric theory 𝓖 and starting with an empty model 𝕞, a run of the chase consists of repeated
applications of the [chase-step](#step) to augment 𝕞 with *necessary* information until there is a 
contradiction or 𝕞 satisfies 𝓖. Inspired by [Steven Vickers][vickers], we refer to the units of information 
for augmenting models as *observations*.

[chase]: https://en.wikipedia.org/wiki/Chase_(algorithm)

### <a name="step">Chase-Step</a>
Given a geometric theory 𝓖 and a model 𝕞, a chase-step proceeds as below:

1. A sequent 𝜑 ⊢<sub>𝘅</sub> 𝜓 from 𝓖 is selected for evaluation.

1. Given an assignment from the variables in 𝘅 to the elements of 𝕞: if 𝜑 is true and 𝜓 is false in 𝕞, 
new observations are added to 𝕞 to make 𝜓 true, such that:

    - If 𝜓 is equal to ⟘ (i.e., an empty disjunction), the chase fails on 𝕞.

    - If 𝜓 contains more than one disjunct, namely 𝜓<sub>1</sub> ∨ ... ∨ 𝜓<sub>i</sub> (i > 1),
    the chase branches and augments clones of 𝕞 to make 𝜓<sub>i</sub> true in each branch.

    - If there is no sequent such that 𝜑 is true and 𝜓 is false in 𝕞, the model 𝕞 already satisfies 
    𝓖 and is returned as an output.

[vickers]: https://www.cs.bham.ac.uk/~sjv/GeoZ.pdf

### Termination

It can be shown a run of the chase always terminates on an unsatisfiable theory, although it may take
a very very long time. However, when the theory is satisfiable, a run of the chase may not terminate, 
producing infinitely large and/or infinitely many models. This is consistent with semi-decidability
of the satisfiability problem for first-order theories.

> **Note:** As discussed [earlier][termination], Razor accepts a search bound to guarantee termination
of the chase.

[termination]: ./razor.html#unbounded
