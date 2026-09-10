# Selected Modelica grammar

The reference is
[`crates/rumoca-phase-parse/src/modelica.par`](https://github.com/CogniPilot/rumoca/blob/a1daf47556c1a6ffd7f4b203235ff09711089a85/crates/rumoca-phase-parse/src/modelica.par)
in the neighboring Rumoca checkout. The requested older `crates/parser` path
has moved on this branch. The upstream file describes itself as the Modelica
3.7-dev grammar for parol; it is an implementation reference, not the published
Modelica standard itself.

`Modelica.ebnf` keeps its production names, single-quoted terminals,
colon definitions and implicit concatenation. The seven used keyword
productions are copied verbatim. Other productions deliberately select fewer
alternatives; they are not represented as verbatim full Modelica productions.
The Lean EBNF reader also accepts the previous `name = ...` / comma dialect.

| Reference production family | Restriction in this file |
| --- | --- |
| Stored/class definition | Exactly one long model; no within, final, encapsulated, partial, inheritance or class descriptions |
| Composition | Exactly the unit profile or the input/output profile, without mixing their declaration and equation forms |
| Component clause/declaration | Only Real, one variable per clause; no arrays, bindings, conditional components or additional prefixes |
| Modification | Exactly two identifiers in order, with values `0` and `true`; resolution requires their names to be `start` and `fixed` |
| Equation | Exactly `der(IDENT)=1` or the matching driven profile's `der(IDENT)=IDENT` |
| Identifier | Existing checked ASCII unquoted identifier lexer; no parol regex directive or quoted identifier alternative |

Parol `%...` directives, Rust type annotations, `@...` action labels and `^`
discard markers are omitted. They configure parol's lexer/actions and do not
belong in this Lean grammar. Modelica comments remain outside the selected
source lexer; `//` here comments the EBNF specification itself.

The generated DFA recognizes both selected syntactic profiles. The production
compiler and actual-C certificate currently admit only the unit profile.
The driven action/IR development is checked separately and must acquire its
target execution and actual-artifact contracts before becoming an FMU path.

Regenerate both checked and runtime tables with `lake run generate`. The full gate
checks freshness and rejects an actual grammar file changed after generation.
