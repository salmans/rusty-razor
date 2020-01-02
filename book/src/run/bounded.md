### Bounded Model-Finding

Unlike conventional model-finders such as [Alloy](http://alloytools.org), Razor doesn't require the user to provide a
bound on the size of the models that it constructs. However, Razor may never terminate when running on theories with
non-finite models -- it can be shown that a run of Razor on an unsatisfiable theory (i.e., a theory with no models)
is guaranteed to terminate (although it might take a very very long time).This is a direct consequence of
semi-decidability of first-order logic.

To guarantee termination, limit the size of the resulting models by the number of their elements using the `--bound`
option with a value for the `domain` parameter:

```
razor solve -i <input> --bound domain=<number>
```

