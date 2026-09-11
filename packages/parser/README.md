# Generic EBNF parser engine

This independently buildable Lake package owns `Parser.*`: the EBNF reader,
DFA and LALR generators, table runtimes, configurable scanner, source ranges,
located concrete syntax trees, bounded parallel mapping, and their proofs.
It depends on Std/mathlib and the separate proof audit tooling. It imports no
language frontend, compiler IR, or backend.

Language definitions live in sibling packages:

- [Modelica](../modelica-parser/README.md): its EBNF, generated DFA tables,
  lexer policy, AST actions, resolution and located/parallel entry points.
- [GALEC](../galec-parser/README.md): its EBNF, generated LALR tables, scanner
  configuration, syntax and semantic actions.

From the root workspace, inside `nix develop`:

```sh
lake build check-parser parser/ebnfgen parser/lalrgen
lake exe ebnfgen --namespace Example.Generated example.ebnf Example.lean
lake exe lalrgen --namespace Example.Generated example.ebnf Example.lean
```

`ebnfgen` compiles the regular, acyclic EBNF profile through regex derivatives.
Its optional `--runtime` mode emits execution tables; the language instance owns
the equality proof against the certified tables. `lalrgen` accepts recursive
productions and emits LALR candidate tables with structural safety and FIRST
certificates. Both generators accept an explicit namespace; neither hardcodes
Modelica or GALEC.

The LALR engine proves accepted trees derive their token sequences and validates
table/stack safety. It does **not** yet prove universal generator completeness
or that every supplied grammar is LALR(1). Conflicts and resource-limit failures
are reported during preprocessing. See [remaining parser proofs](../../dev/lalr-parser.md).

Generated LALR instances expose `parseLocated`. UTF-8 spans and terminal spellings
are checked against source contents; parent ranges cover their descendants.
AST shape and selection of meaningful node origins remain language-owned.
Generic located-parser completeness and location transport through every IR
remain open; see [provenance](../../dev/provenance.md).

The generic token attachment uses a tail-recursive accumulator. In
`Parser.LocatedProofs`, `Parser.Source.attach_eq_reference` proves
the exact public result equals its reference cursor specification;
`Parser.Source.lexLocated_eq_reference` also preserves complete located-lexer
results and diagnostics. The proofs apply to arbitrary token streams and trivia
policies. They accompany the repair of the native long-token stack overflow in
the [performance audit](../../dev/performance-audit.md#pa01-repair-exact-attachment-refinement).

`ParserChecks` owns the engine's axiom audit and existing kernel regressions.
The configurable scanner prefers a matching two-character symbol before an
enabled single-character symbol. `ScannerRefinement.lex_disjoint` (namespace
`Parser.Scanner`) proves exact results and errors for configurations with
disjoint prefixes. The proof-only reference adds no runtime fallback.
`lake test` in this package builds those checks; the root `lake test` additionally
checks actual artifacts and all language/backend integration boundaries.
