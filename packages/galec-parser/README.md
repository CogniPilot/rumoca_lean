# Tiny GALEC frontend

This Lake package instantiates the generic [parser engine](../parser/README.md).
Its [EBNF](grammar/GALEC.ebnf) generates `GALECParser/Generated.lean` through the
engine's `lalrgen` executable. Scanner configuration, syntax values, semantic
actions and the concrete grammar certificates live here, outside the engine.
The language API is `Rumoca.GALEC.Syntax`; it imports no compiler IR or backend.

From the root workspace, inside `nix develop`:

```sh
lake build check-galec-parser
lake run generate
lake run check-generated
```

The root generation command supplies `--namespace Rumoca.GALEC.Generated`.
Generated tables include checked structural safety, FIRST/nullable coverage,
and a generic located-tree entry point. Language-owned actions decode that
syntax into the tiny GALEC block; EBNF alone does not define semantic AST meaning.
`GrammarProofs.lean` binds the actual EBNF preprocessing result to these tables.

`GALECParserChecks` audits the selected syntax round trip, parsing and table
contracts. The eFMI backend separately proves the relationship to GALEC/Solve
IR and emitted artifacts. These language-instance proofs do not establish
universal LALR completeness or full eFMI compliance. See the
[grammar restrictions](grammar/README.md) and [standards review](../../dev/efmi.md).
