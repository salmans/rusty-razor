## Syntactic Variations

Razor supports three syntactic variations of the logical symbols in the input:

* __alpha__ where logical symbols are written as alphabetic words.
* __compact__ where ASCII notations represent logical symbols.
* __math__ where (Unicode) mathematical symbols are used.

> __Note:__ Currently, Razor's parser accepts inputs that are comprised of any combination
of the syntactic variations mentioned above. However, future releases of Razor may restrict
the input to use only one of the variations above.

The table below shows all syntactic variations of the logical symbols:

| symbol                   | alpha      | compact                          | math         |
| ------------------------ |:----------:| :-------------------------------:|:------------:|
| _truth_                  | `true`     | <code>'&#124;'</code>            | `⊤` (U+22A4) |
| _falsehood_              | `false`    | <code>&#95;&#124;&#95;</code>    | `⟘` (U+27D8) |
| _negation_               | `not`      | `~`                              | `¬` (U+00AC) |
| _conjunction_            | `and`      | `&`                              | `∧` (U+2227) |
| _disjunction_            | `or`       | <code>&#124;</code>              | `∨` (U+2228) |
| _implication_            | `implies`  | `->`                             | `→` (U+2192) |
| _bi-implication_         | `iff`      | `<=>`                            | `⇔` (U+21D4) |
| _existential quantifier_ | `exists`   | `?`                              | `∃` (U+2203) |
| _universal quantifier_   | `forall`   | `!`                              | `∀` (U+2200) |