# Selected Modelica grammar

The reference is
[`crates/rumoca-phase-parse/src/modelica.par`](https://github.com/CogniPilot/rumoca/blob/a1daf47556c1a6ffd7f4b203235ff09711089a85/crates/rumoca-phase-parse/src/modelica.par)
in the neighboring Rumoca checkout. The requested older `crates/parser` path
has moved on this branch. The upstream file describes itself as the Modelica
3.7-dev grammar for parol; it is an implementation reference, not the published
Modelica standard itself.

`Modelica.ebnf` keeps its production names, single-quoted terminals,
colon definitions and implicit concatenation. The eight used keyword
productions are copied verbatim. Other productions deliberately select fewer
alternatives; they are not represented as verbatim full Modelica productions.
The Lean EBNF reader also accepts the `name = ...` / comma dialect.

| Reference production family | Restriction in this file |
| --- | --- |
| Stored/class definition | Exactly one long model; no within, final, encapsulated, partial, inheritance or class descriptions |
| Composition | Unit, scalar driven, array driven, array square/Jacobian, constant-rate, or expression profile; their declaration and equation forms remain separate |
| Component clause/declaration | Only Real, one variable per clause; the array profile requires `[2]` input/state and its Jacobian output requires `[2,2]`; no bindings or conditional components |
| Modification | Exactly two identifiers in order, with values `0` and `true`; arrays require `each` on both; resolution requires `start` and `fixed` |
| Equation | Unit `der(IDENT)=1`, driven `der(IDENT)=IDENT`, or one pointwise product plus a Jacobian output equation |
| Expressions/calls | Exactly `IDENT .* IDENT` and `IDENT(IDENT .* IDENT, IDENT)` in the array square profile; the expression profile adds recursive arithmetic over `+ - * /` with unary minus and parentheses, stratified for the MLS operator precedence; no general functions, relations, indexing or matrix products |
| Identifier | Existing checked ASCII unquoted identifier lexer; no parol regex directive or quoted identifier alternative |

Parol `%...` directives, Rust type annotations, `@...` action labels and `^`
discard markers are omitted. They configure parol's lexer/actions and do not
belong in this Lean grammar. Modelica comments remain outside the selected
source lexer; `//` here comments the EBNF specification itself.

`jacobian` is an ordinary identifier, not a reserved keyword. The AST retains
the callee and both arguments; resolution selects the intrinsic and checks the
square/input references. Unknown callees still parse and receive a resolution
diagnostic at their own source span. This direct-expression Jacobian is a
Rumoca extension, not a standard Modelica built-in.

The selected array declarations, same-shape `.*`, and `each` initialization
follow [MLS 3.7 §10.1/§10.6.3](https://specification.modelica.org/maint/3.7/arrays.html)
and [§7.2.5](https://specification.modelica.org/maint/3.7/inheritance-modification-and-redeclaration.html#modifiers-for-array-elements).
Only the small forms above are implemented; the full standard also permits
other dimensions and expressions.

The generated LALR parser recognizes these selected syntactic profiles.
Production publication has separate checked paths for the unit profile, the
tensor square/Jacobian profile and the constant-rate profile. The tensor path
publishes FMI 3 FMUs, eFMI Algorithm Code and complete eFMUs; the constant-rate
path publishes FMI 3 FMUs. Publication still requires the corresponding fixed
actual-artifact checker: successful parsing alone does not admit an arbitrary
model or export format. Driven and expression profiles remain development
cases. The array located API is `Rumoca.ArrayProfile.parseLocated` from
`ModelicaParser.Array.Located`; the LSP still uses the unit-profile document API.

## Structural grammar repair

The profile-specific composition alternatives, especially `jacobian_body`, are
not the intended permanent grammar structure. The next cutover must use ordinary
declarations, equations, expressions and function calls, following the selected
MLS production families. `jacobian` remains an identifier resolved after parsing;
renaming its special production is not a structural repair. Existing checked
profile records may remain semantic lowering inputs, but must not determine
syntax through whole-token-list recognition.

The updated implementation reference for that work is
[Rumoca's Parol grammar at `f477d0b`](https://github.com/CogniPilot/rumoca/blob/f477d0b698954b5a70f86286aaae9a3570ef39d5/crates/rumoca-phase-parse/src/modelica.par).
This does not change the provenance pin of the current EBNF above. The pinned
MLS remains normative; do not copy the entire upstream grammar or assume every
Parol alternative is the chosen MLS subset. The reusable-core sequence and
proof obligations are in [the parser design](../../../dev/lalr-parser.md#structural-modelica-actions).
Open [stage findings](../../../dev/standards-review.md#required-review-at-every-spiral-stage)
still block grammar expansion, including recognition-only expansion. Generic
CST infrastructure may be developed without changing either language grammar,
production parser path or source admission.

Regenerate both checked and runtime tables with `lake run generate`. The full gate
checks freshness and rejects an actual grammar file changed after generation.
