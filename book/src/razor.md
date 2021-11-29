## Razor: A First-Order Approach

Razor takes a direct approach to first-order model-finding without propositionalization and SAT solving. 
The essence of Razor's algorithm is the [chase] from database theory. Our approach to model-finding has a 
couple of primary advantages: first, the model-finding algorithm doesn't inherently require a bound for 
propositionalization. Second, the algorithm can leverage information in first-order logic to guide the search 
for models, unlike the SAT-based approach where the underlying SAT solver is put in charge of the search. However, 
these features usually come at a performance cost as Razor doesn't make use of the blazingly fast modern SAT-solvers.

[chase]: https://en.wikipedia.org/wiki/Chase_(algorithm)

### <a name="unbounded"/> Unbounded Algorithm

As discussed earlier, SAT-based model-finders translate the input first-order theory to a propositional formula up to a bound, 
which is often provided by the user. Providing a search bound that is sufficient for a complete analysis yet small enough to 
make the search tractable poses a challenge to using SAT-based model-finders. Inferring a sufficient search bound to help the 
user has been an ongoing research in the literature.

In contrast, Razor's model-finding algorithm is unbounded: starting from an *empty* model 𝕞 (i.e., a model over an empty 
domain), Razor constructively augments 𝕞 with necessary elements and facts until 𝕞 satisfies the input theory or a 
contradiction occurs. When there is more than one way to continue, the algorithm augments clones of 𝕞 in different search branches.

As a direct result of undecidability of first-order logic, a run of Razor on an arbitrary theory may fail to terminate. 
To guarantee termination, we would need to devise a termination condition such an execution timeout, a count of generated models, 
a maximum search depth, or possibly a bound on the domain size of models. Because of the inherent unboundedness of Razor's algorithm, 
the user wouldn't have to provide the search bound upfront; in fact, the user may let the search continue for an arbitrary length of 
time and kill the Razor's process on demand.

> **Note:**
Some SAT-based model-finders like Paradox implement clever algorithms to reuse some components of the intermediate propositionalized 
formula for a bound of size `n` to generate a propositional formula for a bound at `n + 1`. This approach enables the solver to perform 
incremental model-finding as it expands the search bound. Nevertheless, at each step, a considerable portion of the previously generated 
propositional formulae and the earlier work of the SAT-solver must get discarded.

### Controlled Search

Conventional model-finders put their (often off-the-shelf) SAT-solvers fully in charge of constructing structures 
that are then translated to models of the input theory; therefore, the model-finding tool has little control over 
the search algorithm. In particular, relying on a SAT-solver would limit the opportunities to guide the search and 
optimize the quality of models.

Razor constructs models that are minimal with respect to their *information content* within a framework for *exploring* 
the space of models of the input theory. In addition, employing a first-order search algorithm enables Razor to trivially 
parallelize and distribute the search, give access to the intermediate *partial* models, and employ heuristics to guide the 
search.

#### <a name="minimality"/> Minimality

SAT-based model-finders tend to output *noisy* models: these are non-minimal models which hold *facts* that aren't necessary 
for satisfying the input theory. Noisy models can be hard to understand as they don't offer *provenance* 
for their content. In contrast, Razor's algorithm is guided towards producing *minimal* models, which contain nothing but facts 
that must be present for satisfying the theory. Formally speaking, Razor returns models that are minimal with respect to a 
[homomorphism] ordering on all models of the theory. The homomorphism ordering serves as a useful measure of information 
content, enabling Razor to offer *provenance* to justify the content of its models by the sentences of the input theory.

Consider the [list] specification from the previous section. A run of Razor bounded by a domain size of 4 elements outputs 
models such as the ones below:

- `'my_list` of length 0 (i.e., the `'nil` list):

  `'my_list`: &nbsp;◯

- `'my_list` of length 1:

  `'my_list`: &nbsp;⬤➝◯
  
- `'my_list` of length 0 (an alias for `'nil`) and an unnamed list of of length 1:

  `'my_list`: &nbsp;◯  
  (unnamed): &nbsp;&nbsp;⬤➝◯
  
- `'my_list` of length 2:

  `'my_list`: &nbsp;⬤➝⬤➝◯
  
- `'my_list` of length 0 and an unnamed list of of length 2:

  `'my_list`: &nbsp;◯  
  (unnamed): &nbsp;&nbsp;⬤➝⬤➝◯

- `'my_list` of length 3:

  `'my_list`: &nbsp;⬤➝⬤➝⬤➝◯
  
All these models are minimal in the sense that unlike [some examples][examples] from the previous section, 
every peice of information in these models is required by the input theory and cannot be removed.

> **Note:**
For every model 𝕟 of the input theory 𝓣, Razor returns a model 𝕞 with a homomorphism from 𝕞 to 𝕟. Informally,
it's always possible to construct any model of 𝓣 by adding more information to a model returned by Razor. Therefore, we
refer to the models returned by Razor as a *set of support* for 𝓣.

[homomorphism]: https://en.wikipedia.org/wiki/Homomorphism
[list]: ./model-finding.html#list_example
[examples]: ./model-finding.html#list_example_bad_model

#### Verification and Exploration

First-order model-finding is often applied to uncover inconsistencies and logical flaws where the user verifies if an assertion 
follows from a specification. The assertion, which is often a desirable *property* of the system, holds if its negation is 
inconsistent with the specification, having no models. I will refer to this mode of interaction with a model-finder as 
*verification*. When working with a model-finder in the verification mode, only one (unexpected) model is sufficient to reveal 
a bug in the specification.

In a different mode of analysis, the user understands models of the theory as instances of the behavior of a system specification. 
I will call this mode of interaction with a model-finder *exploration*. Unlike the verification mode, where the model-finder helps 
the user to prove properties of a system, the user of the exploration mode is interested in investigating examples of a system's 
execution without necessarily having specific properties in mind. The goal of exploration is to help the user develop a better 
understanding of the specified system.

> **Note:**
`check` and `run` commands in Alloy operate in verification and exploration modes respectively.

SAT-based model-finders commonly offer models in no particular order as the order of output is dictated by the underlying 
SAT-solver. This behavior is often acceptable in the verification mode, where any counterexample suffices to disprove a hypothesis 
or invalidate a property. In contrast, effective model-finding for exploration greatly benefits from a systematic approach to 
presenting models, an exploration method that enables the user to effectively navigate through various classes of (possibly many) 
models of the theory and does not solely rely on the serendipity of SAT-solving. Razor's approach to model-finding offers a solution!

As I mentioned in the [previous section](#minimality), Razor produces models that are minimal with no noise, i.e., unnecessary facts. 
More accurately, these are models that are minimal with respect to a preorder ≺ induced by the homomorphism relation 
between the models of the theory. For two models 𝕞 and 𝕟 of a theory 
𝓣, 𝕞 ≺ 𝕟 if and only if there is a homomorphism from 𝕞 to 𝕟 and it's easy to show that 𝕞 contains less noise than 𝕟. 
It is, though, always possible to *augment* 𝕞 with additional (unnecessary) facts to obtain 𝕟. This is the core principle that 
enables a framework for model exploration with respect to a measure of information content.

> **Note:**
[Aluminum] is a preliminary realization of this approach to exploring models, which was implemented as a modification of Alloy.

[Aluminum]: https://dl.acm.org/doi/10.5555/2486788.2486820

#### Fitness

Model-finders could potentially incorporate heuristic measures to prioritize specific search branches or adopt various search strategies. 
However, delegating the search to a SAT-solver dramatically limits the opportunity for taking advantage of heuristics and contextual 
information. 

Earlier, I brought up [minimality](#minimality) as a quality measure but the user might be interested in other attributes and criteria 
for model exploration. For example, the user could ask for a new model that is less similar to the ones previously returned or one that 
would be "surprising". Also, the model-finder may keep track of various heuristics to deprioritize search branches that are more likely 
to fail or to switch between different scheduling algorithms.
