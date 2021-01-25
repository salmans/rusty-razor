# rusty-razor

Rusty Razor is a tool for constructing finite models for first-order theories. The model-finding algorithm is inspired
by [the chase](https://en.wikipedia.org/wiki/Chase_(algorithm)) for database systems. Given a first-order theory,
Razor constructs a set of *homomorphically minimal* models for the theory.

Check out Razor's [documentation](https://salmans.github.io/rusty-razor/intro.html) for more information about the project and introductory examples.

## Build

rusty-razor is written in Rust, so you will need [Rust](https://www.rust-lang.org) 1.48.0 or newer to compile it.
To build rusty-razor:

```
git clone https://github.com/salmans/rusty-razor.git
cd rusty-razor
cargo build --release
```

This puts rusty-razor's executable in `/target/release`.

## Run

### `solve`

Use the `solve` command to find models for a theory written in an `<input>` file:

```
razor solve -i <input>
```

The `--count` parameter limits the number of models to construct:

```
razor solve -i <input> --count <number>
```

#### Bounded Model-Finding

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

#### Model-Finding Scheduler

Use the `--scheduler` option to choose how Razor processes search branches. The `fifo` scheduler (the default scheduler)
schedules new branches last and is a more suitable option for processing theories with few small satisfying models.
The `lifo` scheduler schedules new branches first, and is more suitable for processing theories with many large models.

```
razor solve -i <input> --scheduler <fifo/lifo>
```

## Toy Example

Consider the following example:

```
// All cats love all toys:
forall c, t . (Cat(c) and Toy(t) implies Loves(c, t));

// All squishies are toys:
forall s . (Squishy(s) implies Toy(s));

Cat('duchess);   // Duchess is a cat
Squishy('ducky); // Ducky is a squishy
```

You can download the example file [here](https://github.com/salmans/rusty-razor/blob/master/theories/examples/toy.raz) and run the `razor` command-line tool on it:

```
razor solve -i theories/examples/toy.raz
```

Razor returns only one model with `e#0` and `e#1` as elements that denote `'duchess` and
`'ducky` respectively. The facts `Cat(e#0)`, `Squishy(e#1)`, and `Toy(e#1)` in the model
are directly forced by the last two formula in the input theory. The fact `Loves(e#0, e#1)`
is deduced by Razor:

```
Domain: e#0, e#1

Elements: 'duchess -> e#0, 'ducky -> e#1

Facts: Cat(e#0), Loves(e#0, e#1), Squishy(e#1), Toy(e#1)
```

Razor's documentation describes the [syntax](https://salmans.github.io/rusty-razor/syntax.html)
of Razor's input and contains more [examples](https://salmans.github.io/rusty-razor/example.html).
