# Tiny Modelica frontend

This Lake package instantiates the generic [parser engine](../parser/README.md).
It owns the selected [Modelica EBNF](grammar/Modelica.ebnf), generated LALR tables,
Modelica lexical policy, AST and actions, resolution, source locations and
bounded parsing of independent files. The semantic API remains in `Rumoca`;
its implementation modules are `ModelicaParser.*`.

From the root workspace, inside `nix develop`:

```sh
lake build check-modelica-parser
lake run generate
lake run check-generated
```

The coordinating generation command runs `lalrgen` with explicit language
namespaces. Modelica and GALEC use the same reusable engine, EBNF lowering and
checked input-size bound. Language ASTs and resolution never become dependencies
of the engine. The old DFA generator and runtime have been removed.

`Grammar.lean` and the development profile modules derive AST token membership
from the source EBNF equations. `Actions.lean` instantiates the generic
`LALR.TokenParser.Actions` contract; frontends may consume the CST and original
token payloads while defining their own AST relation. The parser/action
soundness and completeness theorems apply to that relation, rather than relying
on execution of a fixed token pattern. This cutover adds no grammar case;
see the [grammar restrictions](grammar/README.md) and
[verification boundary](../../docs/verification.md).

The optional `modelica_parser/frontend-bench` executable measures existing
read/lex/parse/located stages without importing artifact backends. Run it through
`lake run benchmark-frontend`; raw measurements stay under `build/` and are
independent of the proof gate. The [performance audit](../../dev/performance-audit.md)
records the original span-attachment failure, its checked refinement and the
remaining allocation findings.

`ModelicaParserChecks` audits the source lexer, grammar, AST actions and parser
contracts, exact identifier spans and sequential/parallel equivalence.
Name errors include the offending occurrence and a related declaration span;
the error-location theorem binds both ranges to their actual AST fields and
exact source text. The same structured diagnostic feeds terminal and LSP clients.

`ModelicaParser.Array.Located` exposes the separate array/AD frontend under
`Rumoca.ArrayProfile`. Its EBNF, decoder soundness/completeness, recognition and
source-bound call/operand ranges are checked. `jacobian` uses ordinary call
syntax and is selected by resolution. See [the array/AD scope](../../dev/tensor-ad.md)
for its two fixed profiles and the outstanding production lowering contracts.
