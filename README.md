# rusty-razor

Rusty Razor or simply Razor is a tool for constructing finite models for first-order theories. The model-finding algorithm is inspired by [The Chase](https://en.wikipedia.org/wiki/Chase_(algorithm)) for database systems. Given an input first-order theory, Razor constructs a set of *homomorphically minimal* models for the theory. To learn more about the theoretical foundation of Razor, check out my [PhD dissertation](https://digitalcommons.wpi.edu/etd-dissertations/458/).

## Build

You can build it using Cargo, so you will need [Rust](https://www.rust-lang.org). The rest is straight forward:

```
cargo build --release
```

## Run

### `solve`

Use the `solve` command to find models for a theory written in an `<input>` file:

```
razor solve -i <input>
```

The `--count` parameter limits the number of constructed models:

```
razor solve -i <input> --count <number>
```

#### Bounded Model-Finding

Unlike conventional model-finders such as [Alloy](http://alloytools.org), Razor doesn't require the user to provide a bound on the size of the models that it constructs. However, Razor may fail to terminate when running on theories with non-finite models -- it can be shown that a run of Razor on unsatisfiable theories (i.e., theories with no models) is guaranteed to terminate (but it might take a very very long time). This is a direct consequence of semi-decidability of first-order logic.

To guarantee termination, limit the size of the resulting models by the number of their elements, use the `--bound-domain` option:

```
razor solve -i <input> --bound-domain <number>
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

The model contains only one element `e#0` in its domain. This element denotes `'gregor`, a constant in the theory that represents Ser Gregor. The model also contains two facts: `Man(e#0)` is a fact that is directly derived from the second statement in the theory (i.e., `Man('gregor)`). The fact `MustDie(e#0)` is deduced by Razor according to the first statement of the theory.

> Notice that the previous model is a "minimal" model for the given theory. The element `e#0` is required to represent the constant `'gregor`; the fact `Man(e#0)` must be present because the theory states so; and, the fact `MustDie(e#0)` must be true as the result of the first statement. Removing any piece of information makes the given structure a non-model of the theory.

### Golden Head
While reading "The Lineages and Histories of the Great Houses of the Seven Kingdoms", Lord Eddard Stark learns that throughout the history, all male members of House Baratheon were described as "black of hair". Ned concludes that King Robert cannot be Prince Joffrey's real (biological) father. A judgment that eventually cost his life.

The next theory describes Ned's thought process:

```
// A person cannot be both "black of hair" and "golden head"
not (BlackOfHair(x) & GoldenHead(x));

// Traditionally, children inherited their father's family name
Baratheon(x) & father(y) = x -> Baratheon(y);

// King Robert Baratheon has black
Baratheon('robert) & BlackOfHair('robert);

// King Robert is Joffrey's father
father('joffrey) = 'robert;

// Joffrey has golden hair
GoldenHead('joffrey);

// Ned Stark's discovery
Baratheon(x) -> BlackOfHair(x);
```

We can verify Ned's conclusion by running Razor on this theory  [golden-lion.raz](https://github.com/salmans/rusty-razor/blob/master/theories/examples/golden-lion.raz):

```
razor solve -i theories/examples/golden-lion.raz
```

Razor won't be able to find a model for the previous theory, indicating that the theory is inconsistent. Notice that this theory is perfectly satisfiable (i.e., has a model) in the absence of Ned's discovery (try running Razor after commenting out the last line).