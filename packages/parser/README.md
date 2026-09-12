# Generic EBNF parser engine

This independently buildable Lake package owns `Parser.*`: the EBNF reader,
LALR generator and runtime, typed semantic actions, configurable scanner, source ranges,
located concrete syntax trees, bounded parallel mapping, and their proofs.
It depends on Std/mathlib and the separate proof audit tooling. It imports no
language frontend, compiler IR, or backend.

Language definitions live in sibling packages:

- [Modelica](../modelica-parser/README.md): its EBNF, generated LALR tables,
  lexer policy, AST actions, resolution and located/parallel entry points.
- [GALEC](../galec-parser/README.md): its EBNF, generated LALR tables, scanner
  configuration, syntax and semantic actions.

From the root workspace, inside `nix develop`:

```sh
lake build check-parser parser/lalrgen
lake exe lalrgen --namespace Example.Generated example.ebnf Example.lean
```

`lalrgen` accepts recursive productions and emits LALR candidate tables with
structural safety, FIRST, LR-item, EBNF preservation and execution-bound
certificates. It accepts an explicit namespace and imports neither Modelica
nor GALEC. There is no DFA generator or runtime fallback.

`LALR.Completeness.accepts_iff_parse` proves that a grammar accepts a word exactly
when the checked tables' interpreter accepts it with some finite fuel. This is
universal over grammars and words. `parse_tree` gives the exact sufficient count:
one shift per terminal, one reduction per production node, and EOF acceptance.
The tree exists by a separate theorem about mathlib's CFG derivations; it is
not an assumption supplied by the caller. Structural safety excludes internal
table/tree errors for any input and fuel.

`LALR.Progress.accepts_iff_parse` and `parse_terminates` give a checked linear
input-size bound for all words: valid words are accepted; invalid words reject
without internal errors or fuel exhaustion. Production and state credits are
checked against every rule and actual automaton edge. The generator emits
their proofs and a `parse_correct` contract tied to its actual `parse` entry
point, with a separate `parsed_tree` guarantee. Only two scalar budget
coefficients are used at runtime; credit arrays are proof-only metadata.

`EBNF.Derives` gives independent recursive expression semantics. A finite
structural witness accounts for every source branch and every actual CFG rule;
`Frontend.lower_correct` and `compile_correct` prove language preservation for
the public preprocessing functions. Generated `source_parse_correct` binds the
embedded EBNF reader result to its CFG and the actual `parseSymbols` entry point,
with exact acceptance equivalence and all-input termination. The expression
and lowering witness constants are proof-only. Generic and actual Modelica/GALEC/
recursive certificates pass the package and existing integration gates in
`build/ebnf-stage/build/ebnf-package-staged.log` and `ebnf-integration-staged.log`.
The preceding EBNF main full artifact gate passed in
`build/ebnf-preservation/full-gate.log`, with all 584 recorded inputs unchanged.
The subsequent source cutover also passes its required complete artifact gate
in `build/lalr-source-cutover/full-gate.log`, with all 581 recorded inputs
unchanged and both actual target archives checked and retained.

`LALR.TokenParser.Actions` supplies a reusable interface for user-defined ASTs.
Builders receive the actual CST and original token payloads. Frontends define
an independent AST relation and prove action soundness/completeness and source
grammar membership. `parseWith_iff` composes these obligations with the same
executable LR parser. Generated one-step named-rule equations support source
AST derivations; recursive equations are not automatically unfolded by `simp`.
Modelica and GALEC now use this engine and its generated input-size bounds.

The independent EBNF metalanguage-reader conformance proof remains open, as do
generic located-tree completeness and richer LR rejection diagnostics.
Successful candidate generation for every supported conflict-free grammar is
also a separate obligation. Conflicts and preprocessing limits remain explicit
errors; no claim says every supplied grammar is LALR(1). See
[remaining parser proofs](../../dev/lalr-parser.md).

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
