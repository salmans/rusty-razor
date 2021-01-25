## The Chase

Given a geometric theory and starting with an empty model, a run of the chase consists of repeated
applications of [chase-steps](#step) by which the model is augmented with _necessary_ pieces of
information until there is a contradiction or the model satisfies the theory. Inspired by
[Steven Vickers][vickers], we refer to the units of information that augment models as _observations_.

### <a name="step">Chase Step</a>
Given a geometric theory and an existing model, a chase-step proceeds as follows:

1. A sequent from the theory is selected to be evaluated against the model.

2. The selected sequent is evaluated against the model: given an assignment from the free
variables of the sequent to the elements of the model, if the body of the sequent is true and
its head is not true in the model, new observations are added to the model to make the
sequent's head true.

    2.1. If the sequent is headless, meaning its consequence is falsehood (an empty disjunction),
the chase fails on the given model.

    2.2. If the head of the sequent contains more than one disjunct (with at least one
non-trivial disjunction), the chase branches and satisfies each disjunct independently on clones
of the model.

    2.3. If no sequent can be found such that its body and head are respectively true and false
in the model, the model already satisfies the theory and will be returned as an output of the
chase.

[vickers]: https://www.cs.bham.ac.uk/~sjv/GeoZ.pdf
