## Grammar

The input theory accepted by Razor is defined by the grammar below:

```
LOWER       ::= [a-z_][a-zA-Z0-9_]*
UPPER       ::= [A-Z][a-zA-Z0-9_]*

TRUE        ::= "true"    | "'|'" | "⊤" (U+22A4)
FALSE       ::= "false"   | "_|_" | "⟘" (U+27D8)
NOT         ::= "not"     | "~"   | "¬" (U+00AC)
AND         ::= "and"     | "&"   | "∧" (U+2227)
OR          ::= "or"      | "|"   | "∨" (U+2228)
IMPLIES     ::= "implies" | "->"  | "→" (U+2192)
IFF         ::= "iff"     | "<=>" | "⇔" (U+21D4)
EXISTS      ::= "exists"  | "?"   | "∃" (U+2203)
FORALL      ::= "forall"  | "!"   | "∀" (U+2200)

VARIABLE    ::= LOWER
FUNCTION    ::= LOWER
PREDICATE   ::= UPPER
VARIABLES   ::= VARIABLE ("," VARIABLES)*
TERM        ::= VARIABLE | FUNCTION "(" TERMS? ")"
TERMS       ::= TERM ("," TERMS)*

ATOM        ::= TRUE | FALSE
              | TERM "=" TERM | PREDICATE "(" TERMS? ")"
              | "(" FORMULA ")"
F_NOT        ::= NOT F_QUANTIFIED | ATOM
F_AND        ::= F_NOT (AND F_QUANTIFIED)?
F_OR         ::= F_AND (OR F_QUANTIFIED)?
F_QUANTIFIED ::= (EXISTS | FORALL) VARIABLES "." F_QUANTIFIED | F_OR
FORMULA      ::= F_QUANTIFIED ((IMPLIES | IFF) F_QUANTIFIED)*

THEORY       ::= (FORMULA ";")*
```