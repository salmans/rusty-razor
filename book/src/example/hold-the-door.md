## Hold the Door

Wyllis was a young stable boy when he heard a voice from his future: "Hold the Door!" The voice transformed Wyllis to
Hodor (Hold the door, Holdde door, Hoddedor, Hodor, Hodor...!), putting him on a life-long journey, leading him to the
moment that he saves Bran's life. Indeed, because of this defining moment in his future, Wyllis became Hodor in his past.

#### Linear Time
The theory below describes Hodor's journey assuming that time progresses linearly
[hodor-linear.raz](https://github.com/salmans/rusty-razor/blob/master/theories/examples/hodor-linear.raz)

```
// Wyllis hears "Hold the Door" (at time `t`), then he becomes Hodor in the next
// point of time
HoldTheDoor(t) -> Hodor(next(t));

// Hodor, after turning into Hodor at time "t", holds the Door at some time "tt"
// in future ("tt > t")
Hodor(t) -> ? tt . HoldTheDoor(tt) & After(t, tt);

// These are the rules by which time progresses linearly:
// (1) a point of time "t1" that is the next of "t0" (i.e., "next(t0)") is a point of
// time after "t0" ("t1 > t0")
next(t0) = t1 -> After(t0, t1);

// (2) if a point of time "t1" is after "t0", it is either immediately
// after "t0" (i.e., "next(t0)") or there exists some point of time "t2"
// that is immediately after "t0" and before "t1".
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

Elements: 't_hodor -> e#0, sk#0[e#0] -> e#1, next[e#0], sk#1[e#0, e#1] -> e#2,
next[e#1] -> e#4

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
