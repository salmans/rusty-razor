# rusty-razor

Rusty Razor is a tool for constructing finite models for first-order theories. The model-finding algorithm is inspired
by [The Chase](https://en.wikipedia.org/wiki/Chase_(algorithm)) for database systems. Given a first-order theory,
Razor constructs a set of *homomorphically minimal* models for the theory. To learn more about the theoretical
foundation of Razor, check out my [PhD dissertation](https://digitalcommons.wpi.edu/etd-dissertations/458/).

## Build

rusty-razor is written in Rust, so you will need [Rust](https://www.rust-lang.org) 1.37.0 or newer to compile it.
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