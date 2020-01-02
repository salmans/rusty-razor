## Golden Head

While reading "The Lineages and Histories of the Great Houses of the Seven Kingdoms", Lord Eddard Stark learns that
throughout the history, all male members of House Baratheon were described as "black of hair" and concludes that King
Robert is not Prince Joffrey's (biological) father. A judgment that eventually put his head on a spike.

The next theory describes Ned's thought process:

```
// A person "x" cannot be both "black of hair" and "golden head"
~(BlackOfHair(x) & GoldenHead(x));

// Traditionally, a Baratheon child "y" inherited his/her father's ("x"'s) family name
Baratheon(x) & father(y) = x -> Baratheon(y);

// King Robert Baratheon is black of hair
Baratheon('robert) & BlackOfHair('robert);

// King Robert is Joffrey's father
father('joffrey) = 'robert;

// Joffrey has golden hair
GoldenHead('joffrey);

// Ned Stark's discovery (every Baratheon "x" is black of hair)
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
