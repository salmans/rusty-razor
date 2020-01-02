## Valar Morghulis

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