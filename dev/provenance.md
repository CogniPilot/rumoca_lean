# Source locations, editor services and parallel parsing

Status: 2026-09-11. No additional Modelica or GALEC grammar case is admitted.
This work addresses source provenance; it does not establish requirements
traceability or close the airborne assurance plan in [airborne-assurance.md](airborne-assurance.md).

## Checked foundation

`Parser.Source` uses Lean's `String.Pos` for UTF-8 boundaries. A `Span`
is a half-open, ordered range indexed by its immutable source string. Bounds
and parent-range coverage have kernel proofs. File identity belongs to the
owning snapshot, not to a global counter or an assumed collision-free hash.

`Source.lexLocated` wraps an existing lexer. A cursor pass automatically
attaches ranges, checking the exact source spelling of each token and every
trivia gap, including the suffix through EOF. The independent `Aligned`
relation proves token erasure, exact lexemes, ordering and non-overlap. It
rejects an inconsistent lexer/source pair. Grammar authors supply no offsets.
The current lexer contracts support whitespace trivia and literal token
spellings. Comments or escaped lexical values require an extended contract
before those language cases can be admitted.

`LALR.decorate` automatically annotates all terminals and productions of any
candidate tree. `decorate_erases` preserves every terminal, production number
and nonterminal; `decorate_wellSpanned` proves direct-parent coverage throughout
the tree. Empty productions use the next token's start, or EOF. Parent ranges
include their empty children, so a nullable boundary can include adjacent
trivia. The public `parseLocated` checks that the complete sequence of leaves,
including their ranges, is the supplied input. Its result retains the original
LALR parse certificate and mathlib CFG soundness. The EBNF generator emits this
API automatically for every grammar, including the GALEC instance.

This implementation uses cursor attachment and a separate linear tree pass.
It does not yet fuse location construction into the lexer or shift/reduce
loop. Array lookup and cached node ranges avoid repeated leaf searches or
recursive re-computation of child ranges. No speed parity with parol or ANTLR
is claimed. The generator's existing generic completeness obligations remain
open. Span attachment now has a generic completeness proof under an independent
exact-spelling/trivia contract. Completeness of the LALR tree annotation wrapper
remains open.

`Rumoca.parseLocated` provides the existing Modelica AST plus a source-bound
location sidecar. Its `erases` theorem identifies the same actual production
parser result. Syntax errors identify the first mismatching token or EOF;
resolver failures point to the derivative reference or closing model name.
`LocatedProofs` additionally binds the four identifier accessors to their exact
AST fields and proves the resolved reference/declaration text correspondence.
The compiler now requires this sidecar in every artifact and returns structured
located errors directly. The scalar Flat/DAE/Solve layouts now require indexed
origin traces; the GALEC/Algorithm and tensor paths still need migration.
No IR-to-generated-C source map is currently certified.

Name-resolution errors additionally retain a related declaration span in the
same immutable snapshot. `resolve_error_locations` proves, for every failing
resolution, that the primary occurrence and related declaration are the right
AST fields and that both ranges contain their exact text. It also preserves
the resolver's end-name-before-derivative priority. `resolve_complete` checks
that enriching diagnostics loses no successful resolution. CLI JSON emits a
`related` list of byte spans/messages; terminal output renders each note with
source context. The LSP maps these notes to the current document URI and
UTF-16 ranges, conditional on the client's related-information capability.
`diagnostics_without_related` proves omission for clients without support.
These three roots and the existing LSP/parallel integration checks pass in
`build/diagnostic-locations-frontend.log`. No additional test suite was added.
The complete local gate passed at `df382d0` in
`build/diagnostic-locations-full-gate.log`, including FMI and eFMU artifacts.

## Parallel frontend

`Parser.Parallel.map_eq` proves exact equality to sequential mapping for
every pure analysis function, job budget and input list. The Modelica API also
proves source soundness and preservation of input order and identity. Each
result carries its input snapshot and the equality identifying the actual
located parse. Duplicate paths and identical file contents remain distinct
input entries; completion order cannot rename or reorder a file.

The implementation divides contiguous input chunks and their job budgets,
spawning at most `jobs - 1` standard Lean tasks. It does not create one task
per file. Leaf chunks run sequentially; the calling thread also works. This
is static partitioning by file count. Unequal file sizes can cause imbalance;
dynamic work distribution and size-aware partitioning are later performance
work. Lean's native task runtime, OS scheduling and file reads are outside the
logical scheduler equivalence proof, just as other native Lean execution is.
There is no proved speedup, runtime race-freedom theorem or hardware model.

`rumoca parse --jobs 4 --json A.mo B.mo` exposes the frontend without lowering
IRs or building artifacts. It reads each requested file once, then parses and
checks names in parallel. File reads are currently sequential, and all source
snapshots remain in memory for the batch. Results and errors follow argument
order; a failure does not suppress other files. Cross-file name resolution,
imports and combining models into one compilation unit are not implemented.

## LSP boundary

The separate `packages/lsp` package reuses Lean's JSON-RPC framing, LSP records,
file maps and UTF-16 conversion. Signed document versions have small local
wire records because Lean's corresponding records use natural numbers.
The first server supports full-document synchronization, diagnostics, hover
and definition lookup for the existing Modelica profile. It stores immutable
URI/version/source snapshots and has proofs that older updates cannot replace
newer ones, accepted versions never decrease, and a quiet document has a
successful parse and resolution. Protocol transport, file-map construction
and UTF-16 conversions are tested infrastructure, not compiler theorems.

The server processes messages serially. Parsing is pure and file-local, but
background workers, cancellation, incremental reparse, workspace indexing and
GALEC editor actions are not yet exposed. The parallel batch API does not
imply that this first LSP server schedules edits concurrently.

## Remaining gates before grammar growth

| ID | Requirement | Status |
| --- | --- | --- |
| PV01 | Valid source-indexed spans; exact token text, order and disjointness | Soundness and completeness checked for the exact-spelling/trivia contract; actual Modelica and GALEC lexers discharge the contract |
| PV02 | Automatic grammar-node ranges, epsilon policy and grammar erasure | Modelica located entry point complete; generic LALR annotation-wrapper completeness remains open |
| PV03 | Immutable multi-file identity and deterministic parallel results | Checked pure API; native task/file boundary integration exercised |
| PV04 | Tiny Modelica diagnostics and navigation through an actual LSP session | Implemented, including proved resolution-error/declaration ranges; transport is tested infrastructure |
| PV05 | AST/action field origins with exact identifier/equation meaning | Fixed Modelica field table has exact source leaves and production boundaries; use through all compiler IR occurrences and generic action API remain open |
| PV06 | Flat → DAE → GALEC/Solve origin preservation for every lowering | Scalar Flat/DAE/Solve implemented and checked; GALEC/Algorithm and tensor paths open |
| PV07 | Distinguish source, derived and generated origins; no dummy offset fallback in semantic diagnostics | Required in the scalar chain and initialization notices; remaining products and artifacts open |
| PV08 | Certified C/GALEC printer maps tied to actual output bytes and archive members | Open |
| PV09 | Required compiler/artifact gate, source-map mutation controls and independent review | Existing gate retained; provenance artifact obligations open |

Origins should use compact references into an immutable table, preserving
one origin for a tensor operation rather than enumerating tensor elements.
Derived origins should name the transformation and retain parent origins.
Runtime/ABI/solver-generated code needs an explicit generated origin and its
requirements reference. A source comment or `#line` directive alone is not
an artifact-binding theorem. Requirements-to-proof/test links remain a
separate relation from source-to-generated-code ranges.

### Mandatory provenance policy

Every source AST occurrence and every compiler IR node must have required
provenance. This is a required invariant for the initialization slice, not an
optional diagnostics feature. A bare `Option Span` is insufficient:

- Source origins identify the immutable input entry and a checked range in
  that snapshot. Equal-content files must retain distinct input identities.
- Derived origins name the lowering and retain nonempty parent references.
  Combining equations retains their separate origins, including across files;
  it must not invent one continuous range covering unrelated input.
- Generated origins identify the generating rule or requirement and retain
  the relevant source or IR parents. For default state initialization these
  include the state declaration and the default-selection rule.

Use compact, checked references into an immutable origin table. IR nodes do
not duplicate source strings, file paths or entire origin trees. One tensor
operation has one origin reference regardless of its number of elements.
Pure mathematical values and reusable semantic definitions do not need source
locations; compiler occurrences of those values do. Explicit EOF ranges for
missing-token diagnostics remain valid source locations.

Each lowering must prove preservation of the required origin relation alongside
semantic preservation. At the artifact boundary the printer map must bind
those origins to the actual emitted bytes. Types prevent absent or dangling
origins; proofs must also establish that the supplied origins are the correct
ones. Arbitrary default spans and an uninformative `unknown` origin are not
permitted. An attachment failure is an internal compiler error, never a reason
to continue with a whole-file fallback.

This policy is enforced in the scalar Flat/DAE/Solve chain; it is not yet
enforced throughout all production IRs. PV05–PV09 remain open. The
compiler/artifact migration proves that attachment succeeds for
every accepted source and preserves the existing compiler completeness theorem
without an extra successful-attachment hypothesis. Initialization
diagnostics consume the artifact's mandatory locations directly. These results
must not be presented as completion of the full provenance chain.

`Diagnostics.locateFailure` has been removed: the production driver uses the
located entry point without reparsing failures. The retained `compile_complete`
theorem rules out alignment failures as new exclusions. File I/O and
artifact-validation errors need their own identities and explanations, not
invented Modelica offsets. The current related-location type deliberately
stays within one source snapshot; cross-file resolution is still out of scope.

### Attachment completeness and compiler migration

`Parser.Source.Spelled` describes exact nonempty token spellings separated by
trivia, including the suffix through EOF. It is independent of the attachment
algorithm and the grammar. `CursorProofs` relates Lean's actual UTF-8 `find`,
`nextn` and extraction operations to character-list prefixes, using the standard
string-position and iterator libraries. `attach_complete` composes those lemmas
with the existing accumulator/reference equivalence. Runtime attachment is
unchanged, including its tail-recursive implementation.

`Rumoca.Lexes.spelled` derives that contract from every constructor of the
existing Modelica lexer relation. `Parsed.parseLocated_eq` identifies the total
location construction with the actual public located parser. The production
`compile` now uses that parser and located resolution; `Artifact` requires its
checked `LocatedParsed`. `compile_eq_parsed` and the retained `compile_complete`
prove that the required locations exclude no previously specified valid model.
Actual-file certificate generators use the same total construction and theorem.
The new `fieldSpan` accessor uses `Fin 16` for the current AST and therefore has
no missing-index fallback. Its state-span theorem binds the exact declaration.

The existing audits register 14 new roots, with the unchanged axiom whitelist.
The package gate passed in `build/located-provenance/package-gate.log`, and the
required `lake test` gate passed in `build/located-provenance/full-gate.log`.
The package source inventory remained unchanged throughout that full gate;
the [standards record](standards-review.md#mandatory-located-source-standards-impact)
records the generated FMU/eFMU hashes. Initialization code, cross-file origin
tables, per-IR origin preservation and emitted-byte source maps remain separate
work.

### Shared origin tables and source occurrences

`Parser.Source.Input` is the shared immutable snapshot type; the parallel
frontend now uses it directly. `Parser.Provenance.SourceRef` contains a checked
index into an input array and a span in that exact entry. Names and contents
need not be unique. The array belongs to the compilation; indices do not claim
global identity across unrelated compilation contexts.

`Parser.Provenance.Table` stores an array of source, derived and generated
records. Derived/generated records require a first parent and a rule supplied
by the owning compiler. Every parent must precede the new record, excluding
dangling references and cycles. Checked references retain their table in their
type; append preserves old lookups. `traces_source` proves that every record
reaches a source leaf, and the ancestry lemmas preserve source traces across
append and derivation. These are proof relations, not a runtime ancestor-list
builder. Source strings and origin trees are not copied into each reference.
Array ownership and native allocation costs still require performance review;
there is no new benchmark or amortized-complexity theorem.

`ModelicaParser.Origins` instantiates this generic table for the nine semantic
occurrences of the fixed AST. `OriginProofs.lookup` identifies the exact file
and occurrence for each field; `leaf_text` binds names and the literal RHS to
the actual parsed fields. `production_ranges` and `production_boundaries`
prove containment and exact terminal boundaries for the model, declaration,
equation and derivative expression. A whole-model fallback would violate the
declaration/operand boundary contract. This does not yet require these tables
in Flat/DAE/GALEC/Solve or bind them to emitted bytes.

`Parser.Scanner.lex_locations` extends attachment completeness to every
spelling-preserving configurable scanner. The actual GALEC scanner discharges
that premise; `GALEC.Syntax.Parsed.locations_exist` supplies exact locations
for every checked GALEC parse. The GALEC production driver and IRs still need
their required-origin integration. `Artifact.source_locations` and the two
compiler error-correspondence theorems additionally expose exact current
Modelica source fields and structured resolution failures.

This increment adds 23 roots to the existing package audits. The package gate
passed in `build/origin-tables/package-gate.log`; the required full artifact
gate passed in `build/origin-tables/full-gate.log`, including actual numerical
C, both FMI interfaces, GALEC and checked eFMU publication. The package inventory
in `build/origin-tables/source.sha256` remained unchanged throughout the gate.
The [standards record](standards-review.md#shared-source-origins-standards-impact)
records the final FMU/eFMU identities.
The preceding located-driver checkpoint passed the complete gate before being
committed as `ff6cc7e`; [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34612287910)
also passed. That evidence does not certify subsequent IR-origin or
initialization work. No grammar, numerical lowering or target interface changes
in this origin-table increment.

### Required scalar IR origins and initialization

Actual `Flat.Model`, `DAE.Model` and `Solve.Model` occurrences now require
shape-matched origin traces. Flat checks exact parser fields, DAE names its
coordinate/residual transformations, and Solve records derivative, return and
initialization decisions. Source ancestry is proved from those actual graph
records. A checked reference alone is insufficient: each owning model also
requires its field/rule/parent correspondence proof.

`Source.InputRef` selects a checked entry in the caller's immutable input table.
`Artifact.source_identity` proves that compilation retains that exact context.
Origin references remain compact indices; batched table extension preserves
every older lookup and source-ancestry proof. Parse correspondence is an erased
proposition in the IR context, so that context need not retain runtime token
lists or a parse tree. No new native memory-complexity claim is made.

Initialization notices use the actual prepared plan and source declaration.
The CLI/editor correspondence and exact declaration-span theorems pass the
existing audits. Fixed artifact adapters now quote a file identity and source
bytes together. A staged input's name still differs from its original path;
an original-input-to-archive-member map remains unproved.

The isolated implementation passed its complete package and artifact gates in
`build/literal-call-worktree/build/scoped-package-gate-fixed.log` and
`build/literal-call-worktree/build/scoped-full-gate.log`. It is now integrated
in the main workspace; its final required gate passed in
`build/initialization-provenance/full-gate.log`, with the source inventory
unchanged throughout. GALEC/Algorithm, tensor/FMI operation origins
and actual printer maps remain open. The GALEC origin prototype is not yet a
required invariant of its production model type.

## Generic engine ownership

The parser engine now lives in `packages/parser/Parser`, without language
imports. `packages/modelica-parser` and `packages/galec-parser` own their EBNFs,
generated tables and semantic actions. All 97 pre-split audit roots are retained
across the three package check libraries (51 engine, 36 Modelica, 10 GALEC).
The generator accepts explicit namespaces. No grammar case or semantic contract
was added or weakened by the split; generic completeness and IR provenance
obligations above remain open.
