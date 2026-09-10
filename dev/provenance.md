# Source locations, editor services and parallel parsing

Status: 2026-09-10. No additional Modelica or GALEC grammar case is admitted.
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
open. Completeness of the new attachment/annotation wrappers also remains to
be proved; the current new guarantees concern successful results.

`Rumoca.parseLocated` provides the existing Modelica AST plus a source-bound
location sidecar. Its `erases` theorem identifies the same actual production
parser result. Syntax errors identify the first mismatching token or EOF;
resolver failures point to the derivative reference or closing model name.
`LocatedProofs` additionally binds the four identifier accessors to their exact
AST fields and proves the resolved reference/declaration text correspondence.
The legacy compiler entry point and semantic AST layout have not yet migrated
to this sidecar. No IR-to-generated-C source map is currently certified.

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
| PV01 | Valid source-indexed spans; exact token text, order and disjointness | Checked for successful located lexing |
| PV02 | Automatic grammar-node ranges, epsilon policy and grammar erasure | Checked for successful located parsing; generic wrapper completeness open |
| PV03 | Immutable multi-file identity and deterministic parallel results | Checked pure API; native task/file boundary integration exercised |
| PV04 | Tiny Modelica diagnostics and navigation through an actual LSP session | Implemented, including proved resolution-error/declaration ranges; transport is tested infrastructure |
| PV05 | AST/action field origins with exact identifier/equation meaning | Modelica identifier accessor/AST-field correspondence checked; equation origins and generic action API open |
| PV06 | Flat → DAE → GALEC/Solve origin preservation for every lowering | Open |
| PV07 | Distinguish source, derived and generated origins; no dummy offset fallback in semantic diagnostics | Open for the compiler/IR pipeline; located frontend has explicit EOF/error ranges |
| PV08 | Certified C/GALEC printer maps tied to actual output bytes and archive members | Open |
| PV09 | Required compiler/artifact gate, source-map mutation controls and independent review | Existing gate retained; provenance artifact obligations open |

Origins should use compact references into an immutable table, preserving
one origin for a tensor operation rather than enumerating tensor elements.
Derived origins should name the transformation and retain parent origins.
Runtime/ABI/solver-generated code needs an explicit generated origin and its
requirements reference. A source comment or `#line` directive alone is not
an artifact-binding theorem. Requirements-to-proof/test links remain a
separate relation from source-to-generated-code ranges.

PV07 also requires removing `Diagnostics.locateFailure`: the production driver
currently reparses after failure to reconstruct a located error. Moving it to
the located entry point must preserve source-parser/compiler completeness,
rather than introduce alignment failures as new exclusions. File I/O and
artifact-validation errors need their own identities and explanations, not
invented Modelica offsets. The current related-location type deliberately
stays within one source snapshot; cross-file resolution is still out of scope.

## Generic engine ownership

The parser engine now lives in `packages/parser/Parser`, without language
imports. `packages/modelica-parser` and `packages/galec-parser` own their EBNFs,
generated tables and semantic actions. All 97 pre-split audit roots are retained
across the three package check libraries (51 engine, 36 Modelica, 10 GALEC).
The generator accepts explicit namespaces. No grammar case or semantic contract
was added or weakened by the split; generic completeness and IR provenance
obligations above remain open.
