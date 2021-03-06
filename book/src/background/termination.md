## Termination

As a result of semi-decidability of geometric theories, it can be shown if a geometric theory
is unsatisfiable, a run of the chase on the theory always terminates, although it may take
a very very long time.
However, when the theory is satisfiable, a run of the chase may not terminate, producing
infinitely large models and/or infinitely many models that satisfy the theory. Nevertheless,
in practice, Razor can _bound_ the size of models created by the chase to guarantee termination.

