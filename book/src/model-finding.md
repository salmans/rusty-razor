## Conventional Model-Finding

It's a well-known result that first-order model-finding is undecidable (see [Gödel's incompleteness theorem][godel]). 
As a consequence, any practical model-finding algorithm must resort to some notion of *bound* on the search 
space of models to guarantee termination. Conventional model-finders, such as Kodkod, MACE, and Paradox, 
assume a bound on the size of the domain of models to be found. This assumption makes it possible to translate 
the input first-order theory 𝓣 to a propositional formula 𝓟 up to the give bound. This process is known 
as *propositionalization*. Next, the model-finder utilizes a [SAT][sat] solver to find 
solutions for 𝓟. Intuitively speaking, one might think of the propositionalization step as the process of 
enumerating all potential models of the initial first-order formula where each propositional variable in 𝓟 
represents a *fact* in first-order models of 𝓣. The job of the SAT solver is to find solutions to 𝓟, 
corresponding to images of first-order models for 𝓣. Finally, the model-finder maps the solutions to the 
SAT problem back to models of the original first-order theory 𝓣.

<a name="list_example"></a> 
For example, consider the following specification of a conventional list in functional 
programming languages:

```
// Every list `x` is `'nil` or points to a `next` list:
∀ x . List(x) → x = 'nil ∨ ∃ y. next(x) = y and List(y);

// The `next` of a list is its sublist:
∀ x, y. next(x) = y → Sublist(x, y);
// The `next` of a sublist is itself a sublist:
∀ x, y, z. Sublist(x, y) ∧ next(y) = z → Sublist(x, z);

// `'nil` never point to a `next` list:
~∃ x. next('nil) = x;
// A list cannot be its own sublist (no cycles):
~∃ x. Sublist(x, x);

// `'my_list` is a list:
List('my_list);
```

The first five formulae of this theory describe the list data structure and the last formula asks for models 
with a list, namely `'my_list`. Given a bound of 4 on the size of the models, a conventional model-finder 
queries the underlying SAT solver for solutions consisting of 1, 2, 3, or 4 elements (e.g., lists) that satisfy 
the theory. Consequently, the model-finder may spit out solutions such as the following (○, ●, and ⟶ respectively
denote the `'nil` list, a non-empty list, and the `next` function):

- `'my_list` of length 0 (i.e., the `'nil` list):

  `'my_list`: &nbsp;◯

- `'my_list` of length 1 (a node pointing to `'nil`):

  `'my_list`: &nbsp;⬤➝◯

- `'my_list` of length 2:

  `'my_list`: &nbsp;⬤➝⬤➝◯

<a name="list_example_bad_model"></a> 
- Two lists (`'my_list` and an unnamed list) of length 1:

  `'my_list`: &nbsp;&nbsp;⬤➝◯  
  (unnamed): &nbsp;⬤➝◯

- `'my_list` of length 3 and a (unnamed) list of length 0:

  `'my_list`: &nbsp;&nbsp;⬤➝⬤➝⬤➝◯  
  (unnamed): &nbsp;◯

A key take-away is that the input bound on the model size does not only guarantee termination, but also is 
*necessary* to make propositionalization generally possible.

> **Note:**
Certain classes of first-order formulae including the [Bernays–Schönfinkel–Ramsey class][effective], 
also known as the *effectively propositional* (EPR) class, may be translated into propositional logic without 
an explicit search bound.

[godel]: https://en.wikipedia.org/wiki/Gödel%27s_incompleteness_theorems
[sat]: https://en.wikipedia.org/wiki/Boolean_satisfiability_problem
[effective]: https://en.wikipedia.org/wiki/Bernays–Schönfinkel_class
