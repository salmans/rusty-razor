# Run

## `solve`

Use the `solve` command to find models for an input theory. The `-i` (short for `--input`)
reads the input from a file:

```
razor solve -i <input>
```

> Run `solve` without the `-i` option to read the input from the standard input.

The `--count` parameter limits the number of models to construct:

```
razor solve -i <input> --count <number>
```