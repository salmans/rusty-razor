# rusty-razor

Rusty Razor is a tool for constructing finite models for first-order theories. The model-finding algorithm is inspired
by [The Chase](https://en.wikipedia.org/wiki/Chase_(algorithm)) for database systems. Given a first-order theory,
Razor constructs a set of *homomorphically minimal* models that satisfy the theory. To learn more about the theoretical
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

### Model-Finding Scheduler

Use the `--scheduler` option to choose how Razor processes search branches. The `fifo` scheduler (the default scheduler)
schedules new branches last and is a more suitable option for processing theories with few small satisfying models.
The `lifo` scheduler schedules new branches first, and is more suitable for processing theories with many large models.

```
razor solve -i <input> --scheduler <fifo/lifo>
```

## Examples

### Valar Morghulis!

All men must die. 
Ser Gregor is a man. 

```
// All men must die:
forall x. (Man(x) implies MustDie(x));

// Ser Gregor is a man:
Man('gregor);
```

Run Razor on the previous theory [valar-morghulis.raz](https://github.com/salmans/rusty-razor/blob/master/theories/examples/valar-morghulis.raz):

```
razor solve -i theories/examples/valar-morghulis.raz
```

Razor returns only one model:

```
Domain: e#0

Elements: 'gregor -> e#0

Facts: Man(e#0), MustDie(e#0)
```

The model contains only one element `e#0` in its domain. This element denotes `'gregor`, a constant in the theory that
represents Ser Gregor. The model also contains two facts: `Man(e#0)` is a fact that is derived from the second statement
of the theory (i.e., `Man('gregor)`). The fact `MustDie(e#0)` is deduced by Razor according to the first statement of
the theory.

> Notice that the previous model is a "minimal" model for the given theory. The element `e#0` is required to represent
the constant `'gregor`; the fact `Man(e#0)` must be present because the theory says so; and, the fact `MustDie(e#0)`
must be true because of the first statement. Removing any piece of information makes the given structure a non-model of
the theory.

### Golden Head

While reading "The Lineages and Histories of the Great Houses of the Seven Kingdoms", Lord Eddard Stark learns that
throughout the history, all male members of House Baratheon were described as "black of hair" and concludes that King
Robert is not Prince Joffrey's (biological) father. A judgment that eventually put his head on a spike.

The next theory describes Ned's thought process:

```
// A person "x" cannot be both "black of hair" and "golden head":
~(BlackOfHair(x) & GoldenHead(x));

// Traditionally, a Baratheon child "y" inherited his/her father's ("x"'s) family name:
Baratheon(x) & father(y) = x -> Baratheon(y);

// King Robert Baratheon is black of hair
Baratheon('robert) & BlackOfHair('robert);

// King Robert is Joffrey's father
father('joffrey) = 'robert;

// Joffrey has golden hair
GoldenHead('joffrey);

// Ned Stark's discovery (every Baratheon "x" is black of hair):
Baratheon(x) -> BlackOfHair(x);
```

We can verify Ned's conclusion by running Razor on this theory
[golden-lion.raz](https://github.com/salmans/rusty-razor/blob/master/theories/examples/golden-lion.raz), asking for a
scenario (i.e., model of the theory) that justifies Joffrey's golden head:

```
razor solve -i theories/examples/golden-lion.raz
```

Razor cannot find a model for the previous theory, meaning the theory is inconsistent. Notice that this theory
is satisfiable (i.e., has a model) in the absence of Ned's discovery (try running Razor after commenting out the last
line).

### Hold the Door

Wyllis was a young stable boy when he heard a voice from his future: "Hold the Door!" The voice transformed Wyllis to
Hodor (Hold the door, Holdde door, Hoddedor, Hodor, Hodor...!), putting him on a life-long journey, leading him to the
moment that he saves Bran's life. Indeed, because of this defining moment in his future, Wyllis became Hodor in his past.

#### Linear Time
The theory below describes Hodor's journey assuming that time progresses linearly
[hodor-linear.raz](https://github.com/salmans/rusty-razor/blob/master/theories/examples/hodor-linear.raz)

```
// Wyllis hears "Hold the Door" (at time `t`), then he becomes Hodor in the next point of time
HoldTheDoor(t) -> Hodor(next(t));

// Hodor, after turning into Hodor at time "t", holds the Door at some time "tt" in future ("tt > t")
Hodor(t) -> ? tt . HoldTheDoor(tt) & After(t, tt);

// These are the rules by which time progresses linearly:
// (1) a point of time "t1" that is the next of "t0" (i.e., "next(t0)") is a point of
// time after "t0" ("t1 > t0")
next(t0) = t1 -> After(t0, t1);

// (2) if a point of time "t1" is after "t0", it is either immediately after "t0" (i.e., "next(t0)")
// or there exists some point of time "t2" that is immediately after "t0" and before "t1".
After(t0, t1) -> next(t0) = t1 | ? t2 . next(t0) = t2 & After(t2, t1);

// And we know at some point of time (namely "'t_hodor"), Wyllis became Hodor
Hodor('t_hodor);
```

An unbounded run of Razor on the previous theory will never terminate (feel free to press `ctrl + c` after a
few seconds):

```
razor solve -i theories/examples/hodor-linear.raz
```

Assuming that time progresses linearly, the circular causality between the two events of "holding the door" and
"becoming Hodor" results in an infinitely large model where time progresses unboundedly. We can restrict the size of
the structures constructed by Razor by bounding the number of their elements. For example, if we restrict the number of
elements to 4, Razor will find 9 *incomplete* structures, which do *not* satisfy the theory:

```
razor solve -i theories/examples/hodor-linear.raz --bound domain=4
```

For example, the following structure corresponds to an incomplete model where `e#0` denotes the starting point `t_hodor`
and `e#1`, `e#2` and `e#4` are other points in time:

```
Domain: e#0, e#2, e#4, e#1

Elements: 't_hodor -> e#0, sk#0[e#0] -> e#1, next[e#0], sk#1[e#0, e#1] -> e#2, next[e#1] -> e#4

Facts: After(e#0, e#1), After(e#2, e#1), Hodor(e#0), Hodor(e#4), HoldTheDoor(e#1)
```

Now consider `e#1` and `e#2`. The incomplete model shows that `e#1` is after `e#2`, but neither `e#1`
immediately follows `e#2` (no next point for `e#2`) nor there exists a point that is after `e#2` and
before `e#1`, violating the second rule of linear time progression. In general, it may be possible to extend the
incomplete structure to a model of the theory by adding more information to the model. Any model of this particular
theory, however, is infinitely large.

#### Time-Loop

Next, we model time as a "big ball of wibbly wobbly timey wimey stuff!" To make it simple, let's assume that time-loops
can only happen at the moment that Hodor heard a voice from the future, namely `'t_hodor`, changing our rules of
time progression ([hodor-time-loop.raz](https://github.com/salmans/rusty-razor/blob/master/theories/examples/hodor-time-loop.raz)):

```
HoldTheDoor(t) -> Hodor(next(t));

Hodor(t) -> ? tt . HoldTheDoor(tt) & After(t, tt);

next(t0) = t1 -> After(t0, t1);
After(t0, t1) -> (next(t0) = t1) | ? t2 . next(t0) = t2 & After(t2, t1);

// Hold the door moment only happens at 't_hodor
HoldTheDoor(t) -> t = 't_hodor;

Hodor('t_hodor);
```

In presence of time-loops, Razor can explain Hodor's curious journey:

```
razor solve -i theories/examples/hodor-time-loop.raz
```

This time, Razor produces infinitely many (finite) models with time-loops of different size. Use can use the `--count`
option to limit the number of models and halt the process.
