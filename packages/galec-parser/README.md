# GALEC frontend

This Lake package instantiates the generic [parser engine](../parser/README.md).
Its [EBNF](grammar/GALEC.ebnf) generates `GALECParser/Generated.lean` through the
engine's `lalrgen` executable. Scanner configuration, syntax values, semantic
actions, printing and the concrete grammar certificates live here, outside the
engine. The language API is `Rumoca.GALEC.Syntax`; it imports no compiler IR or
backend.

From the root workspace, inside `nix develop`:

```sh
lake build check-galec-parser
lake run generate
lake run check-generated
```

The root generation command supplies `--namespace Rumoca.GALEC.Generated`.
Generated tables include checked structural safety, FIRST/nullable coverage,
and a generic located-tree entry point. `GrammarProofs.lean` binds the actual
EBNF preprocessing result to these tables.

`StructuralActions` supplies a typed action for every EBNF rule, executed by the
reusable recursive action engine; `ActionCoverage` proves exhaustive coverage and
licensing for the whole grammar. `AST` keeps original token payloads and
categories: names, per-component indices, extents as unevaluated expressions,
calls, dimension queries, nested loops with an optional step, `if` statements
with their ordered branches and optional `else` body, error-signal checks and
statements, and method signal interfaces (empty when absent). A bare number
component becomes a literal; no shape inference or name resolution occurs.

`Syntax.parse` scans once, runs the certified LALR parser once and builds from
that same CST once. `Parsed` carries a `Witness` of the actual tokens, tree,
structural value and typed-action denotation. `erase_parse`, `success_iff`,
`accepts_iff`, `lexical_error` and `successful_tree` characterize the result for
every source string. Declarations, names, shapes and method admission are
static semantics in core elaboration, not parser checks.

`Certificate` provides `certify_source`, which evaluates a closed `String` term
and adds kernel-checked scanner, tree, structural and action equations and the
resulting `Syntax.parse` fact; quotation proposes data only. `Print.block`
renders a syntax tree in the scalar Algorithm Code layout; it carries no proof.
Located parsing attaches exact source ranges to the scanned tokens.

The grammar has 24 rules and 581 canonical / 180 LALR(1) states.

`GALECParserChecks` audits the scanner, parser, action and certificate
contracts, and kernel-checks certificates and printer round trips for the scalar layout and
for every error-signaling form. The eFMI
backend separately proves the relationship to the prepared Solve algorithm
and emitted artifacts. The full artifact gate is required in addition to these owner
checks; see [current evidence](../../docs/verification.md). These proofs do not
establish full eFMI compliance. See the [grammar](grammar/README.md) and
[standards review](../../dev/efmi.md).
