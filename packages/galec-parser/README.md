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
and a generic located-tree entry point. `StructuralActions` supplies a typed
table for every current EBNF rule, executed by the reusable recursive action
engine. Names, ordinary function calls and explicit extents retain their
original token payloads in `AST`; no shape inference or resolution occurs there.
`GrammarProofs.lean` binds the actual EBNF preprocessing result to these tables.

The unresolved AST additionally represents per-component computed indices,
dimension queries and nested `for` loops with an optional explicit step.
These are representation prerequisites, not newly admitted syntax: current
actions construct unindexed references, and the existing exact-profile
projections reject indexed paths and loops. Bounds, static Integer checking,
scope, shapes, mutability and execution belong to subsequent elaboration/proofs.
No Jacobian-specific call constructor is introduced.

The source entrypoints run LALR once and give its actual CST to `StructureBridge`
and `StructuralParser`. Direct AST projections restrict lowering to the existing
verified scalar/tensor profiles. Generic independent `Words` semantics and the
frontend profile proofs establish exact payload yield for arbitrary valid trees,
without reconstructing a canonical tree or assuming CST uniqueness.
Exhaustive coverage/licensing instantiate generic action completeness for the
whole current grammar, not merely accepted examples.

`SourceCompatibility` proves exact `Except` equality with proof-only references
of the previous source entrypoints, including diagnostic text and precedence.
The old token decoders are noncomputable compatibility specifications; the
production parser executes neither them nor a second parse. No grammar or
source-admission expansion follows from this cutover.

`GALECParserChecks` audits the selected syntax, parser, action and compatibility
contracts. The eFMI backend separately proves the relationship to GALEC/Solve
IR and emitted artifacts. The full artifact gate is required in addition to
these owner checks; see [current evidence](../../docs/verification.md).
These proofs do not establish full eFMI compliance. See the
[grammar restrictions](grammar/README.md) and [standards review](../../dev/efmi.md).
