# Compiler performance audit — 2026-09-10

## PA11 — GALEC profile projection host-code expansion (2026-09-22)

The structural-parser cutover at `0f1fecc` passed Lean owner checks, but its
large nested AST profile patterns generated 1,651,291 lines / 54,459,127 bytes
in `packages/galec-parser/.lake/build/ir/GALECParser/ProfileProjection.c`.
This is Lean's native compiler implementation, **not emitted model C**.

During the required full gate, GCC's `cc1` was still active at 8:48 with 99.3%
CPU and 12,206,916 KiB resident memory. Main deliberately terminated that exact
owned compilation process to repair the measured expansion. The gate records
529 seconds and a termination failure (exit 1), not an OOM or a passing gate.
All 2,513 frozen tracked inputs were unchanged. Evidence:
`build/galec-cutover-full-gate-v1.log`, `.exit`, `-inputs.sha256`.

Required repair: compositional AST projections with small helpers, preserving
exact `toScalar`/`toTensor` results for **all** ASTs, including malformed
rejection and raw token categories. Do not flatten/reconstruct tokens, rerun
the parser, assume a valid AST, or weaken the profile predicate. Prove equality
through the existing exact projection/retraction contracts, measure generated
host C and native compilation separately, and rerun the full artifact gate.
The repair is now integrated as small `@[noinline]` AST checks under
`ProfileProjection.Factors`, with unchanged embeddings and six public theorem
statements. Independent helper/exact-image proofs cover every AST; the old giant
matcher is removed, not retained as a fallback. Scratch migration equalities
also prove identical success and rejection against the previous implementation.
All 65 scratch roots passed the unchanged whitelist. Bounded independent Astra
review found no omitted profile check or runtime/proof dependency issue.

The actual integrated owner module generates 5,159 lines / 142,920 bytes of
host C (about 381 times smaller by bytes). Its native object built successfully
in 2.2 seconds; Lean elaboration took 7.2 seconds. Evidence:
`build/galec-projection-factor-native-v1.log` and `.exit` (0).
The scratch-only measurement was 3,917 lines / 94,391 bytes and does not include
the imported embeddings; it is not substituted for the owner measurement.
These are host build measurements, not model execution throughput, whole-build
speedups or embedded WCET. The required full artifact gate for `acf3046`
subsequently passed (V2, exit0), with 2,513 frozen inputs unchanged, all 8,006
complete reports and 126 added roots within the unchanged whitelist, plus four
separately audited retained FMU roots. PA11's observed build failure is repaired;
no asymptotic, whole-MSL or target-C conformance claim follows. Evidence:
`build/galec-cutover-full-gate-v2.*` and
`build/galec-cutover-fmu-retained-v2.*`.
Scratch evidence is under `build/galec-projection-factor-draft/`.

The current implementation is not ready for MSL-scale workloads. Identifier
interning is necessary, but the first measured release blocker was native stack
exhaustion in token-span attachment. Its checked accumulator refinement and
native reproduction results are recorded below. The audit also finds avoidable whole-file
allocation, eager diagnostic rendering, unbounded batch input retention and
representations that will become expensive as IR programs grow. No grammar or
semantic contract has been changed to obtain these measurements.

This is an implementation audit and a native frontend baseline, not a full MSL
compilation, a comparison with ANTLR/parol, a complexity proof or embedded WCET
analysis. Production still admits only the unit-derivative model. The separate
array/AD development profiles do not enable MSL compilation.

## Reproduce and interpret the measurements

Inside the verification shell:

```sh
lake run benchmark-frontend --out build/performance-audit/new-run
lake run benchmark-frontend --stages-only --workload token_rejection_65536 \
  --repeats 1 --out build/performance-audit/stack-reproduction
lake run benchmark-frontend --msl '/path/to/Modelica 4.1.0' \
  --out build/performance-audit/msl-proxy
```

The command builds only the native compiler and the optional frontend package
benchmark. It is outside `lake test`. Unexpected exits make the command fail
while retaining the evidence; the original PA01 reproduction failed this way. Each
sample starts a fresh process after an unrecorded warmup; filesystem caches are
warm. Logs, workload files, raw samples, summaries and corpus inventories stay
under `build/`. No pass stamp or separate proof cache is introduced.

The recorded baseline predates the LALR source cutover; its timings must not
be attributed to the current production parser.

Baseline identity:

- Compiler revision: the previous checkpoint; no compiler
  semantic changes in the measurement checkout.
- Executable: `packages/compiler/.lake/build/bin/rumoca`, SHA-256
  `61b4bb6de3f54f1134519b57293b13e51f1e3d0e3592e37f81ba8591ab392539`.
  Its 145,475,368-byte file size is **not** its resident memory size.
- Lean 4.29.1; Linux 6.18.39, AMD Ryzen 9 5950X, 32 available logical CPUs,
  approximately 64 GiB RAM, 8 MiB soft native stack limit. No concurrent local
  proof build during measurement. Three measured repetitions per workload.
- Authoritative CLI data: `build/performance-audit/measured/summary.json`,
  `samples.jsonl` and `environment.json`; stage data in
  `build/performance-audit/stages/`. These raw files are local ignored artifacts.
- Linux `wait4` supplies per-child peak RSS. For the lightweight stage executable,
  use its own `/proc/self/status` `VmHWM` to exclude the launcher's pre-exec RSS
  floor. An earlier exploratory run in `build/performance-audit/` hashed the
  whole executable in memory and contaminated RSS; its RSS is not this baseline.
  The retained harness streams hashes. Timings below are wall-clock medians;
  a 5 ms process-poll interval limits the precision of very short samples.

The stage executable also prints an internal `elapsed_ns` value after loading
the file. That excludes file I/O and startup; the `read` stage merely observes
the loaded byte count. Use the harness's wall time for the read baseline and
the tables below, rather than interpreting that internal counter as disk time.

The local corpus is the `Modelica 4.1.0/` directory found in Rust Rumoca's
`target/msl/ModelicaStandardLibrary-4.1.0/`; its upstream release is
[MSL 4.1.0](https://github.com/modelica/ModelicaStandardLibrary/releases/tag/v4.1.0).
The inventory below identifies the exact local contents measured.
It contains 2,552 `.mo` files, 14,746,170 bytes, median 1,999.5 bytes, p95 11,683
bytes and maximum 649,910 bytes. Sibling libraries such as ModelicaServices are
excluded. Its sorted path/size/content inventory SHA-256 is
`7bc25e5c34bdb382658981c5b26dc7e4814ece5f33f9c9eb1610471648d1f8bf`.
The proxy preserves that file-size distribution with accepted models and spaces;
it does **not** reproduce token density, nesting, imports, instantiation or
solving. MSL 4.1.0 is based on MLS 3.6; our normative language review targets
MLS 3.7. Those are different versioned artifacts.

| Native CLI workload | 1 worker, seconds / MiB RSS | 4 workers | 8 workers |
| --- | ---: | ---: | ---: |
| One tiny model (startup) | 0.036 / 70.4 | 0.036 / 70.2 | 0.036 / 70.3 |
| 4,000 tiny files | 0.123 / 75.1 | 0.098 / 80.8 | 0.093 / 89.3 |
| One model + 4 MiB spaces | 0.310 / 254.0 | 0.310 / 254.0 | 0.310 / 254.0 |
| 512 files + 64 KiB spaces each | 1.980 / 137.0 | 0.608 / 151.6 | 0.377 / 170.9 |
| 64 files, first 32 padded by 256 KiB | 0.532 / 94.9 | 0.310 / 108.5 | 0.194 / 136.9 |
| Invalid character after 1 MiB spaces | 0.260 / 218.3 | 0.259 / 218.6 | 0.260 / 218.3 |
| MSL file-size proxy, 2,552 files | 0.854 / 111.5 | 0.387 / 166.7 | 0.320 / 200.2 |

The CLI includes reading files, lexing, located parsing, resolution and JSON
serialization. Eight workers improve the proxy's elapsed time by about 2.7×,
with higher memory consumption. These are not whole-compiler throughput rates.
The lightweight stage executable starts around 7.2 MiB RSS; it imports only the
Modelica located parser. It isolates the following costs:

| Input and stage | Median seconds | Post-exec peak MiB RSS | Result |
| --- | ---: | ---: | --- |
| 4 MiB spaces, read | 0.015 | 17.2 | accepted |
| 4 MiB spaces, lex | 0.137 | 156.9 | accepted |
| 4 MiB spaces, plain parse | 0.137 | 156.9 | accepted |
| 4 MiB spaces, located parse | 0.301 | 192.4 | accepted |
| Error after 1 MiB spaces, located parse | 0.041 | 46.0 | diagnostic |
| 65,536 extra semicolons, lex | 0.015 | 19.4 | tokenized |
| 65,536 extra semicolons, plain parse | 0.026 | 21.4 | diagnostic |
| 65,536 extra semicolons, located parse | 0.091 | unavailable | **SIGABRT** |

The semicolon input is only 65,588 bytes. All three measured repetitions and
all CLI worker counts aborted with `Stack overflow detected. Aborting.`;
1,024 and 16,384 extra tokens produced ordinary diagnostics. This is a native
resource failure before a diagnostic, not a counterexample to an idealized Lean
semantic theorem. The repair below replaces attachment rather than increasing
the stack setting. The tables above retain the original failing baseline.

## Findings and proof-preserving work order

| ID / priority | Evidence and consequence | Required change and closure evidence |
| --- | --- | --- |
| PA01 / P0 | The original `Parser/Located.lean`, `Source.attach` recursed through the remaining tokens before constructing the result. `parseLocated` attaches spans before syntax rejection. Isolated stage runs located the observed stack overflow here. | Accumulator implementation and exact refinement proofs now pass; the reproduced native crash is repaired. Full-gate status is recorded below. No input cap or larger stack is used. |
| PA02 / P1 | `ModelicaParser/Lexer.lean` expands the source into `List Char`, with additional identifier slicing; `Parser/Located.lean` scans gaps and spells tokens again. Generated native C confirms substring extraction and character-list allocation. | One UTF-8 cursor scan producing compact token IDs and exact byte ranges. Prove refinement to the lexical and location relations, including error offsets and Unicode boundaries. Stage allocation measurements must demonstrate the saving. The lexer also has non-tail per-token recursion; its larger-input limit is unmeasured, not the cause of the observed 65k crash. |
| PA03 / P1 | Identifier tokens and AST names carry `String`; no frontend interner exists. The C literal pool is unrelated. Passing one string into several records shares it, but repeated occurrences can still allocate distinct spellings. | Add compilation-owned spelling IDs with exact equality after hashing, reverse decoding and stable extension proofs. Keep spelling identity distinct from declaration identity and source occurrence. Measure retained memory and merge peaks, not only wall time. See the interning design below and roadmap E03. |
| PA04 / P1 | `Rumoca/ParseFiles.lean` reads every file sequentially before parsing. `Parser/Parallel.lean` partitions contiguous lists by file count, not bytes/cost. | Bound in-flight source bytes and results; overlap I/O with independent parsing. Preserve ordered outcomes, error spans and sequential equivalence. Use size-aware work distribution and explicit cancellation. A slow earliest result must not allow an unbounded reorder buffer. List partitioning allocates list spines, not copies of source bytes. |
| PA05 / P1 | Full CLI startup is about 70 MiB, versus 7.2 MiB for the isolated parser. `Rumoca.CLI` imports the FMI/eFMI driver and its broad runtime dependency closure. | Profile native initialization and dependencies; separate runtime definitions from proof-only modules where justified. Preserve mathematical libraries for proofs. This finding does not mean proofs are reverified per file; they are erased/cached as appropriate. |
| PA06 / P1 | Generic LALR reduction builds full trees, then checks their validity and token word; located LALR performs additional decoration. Candidate generation uses list item sets and linear searches through productions/states. | Measure generation separately from runtime. Index productions and canonical states; prove emitted tables retain their meaning. Refine runtime stacks/reduction actions to avoid redundant retained trees and checks only where a theorem discharges their purpose. Array action/goto tables and immutable grammar sharing are already good foundations. |
| PA07 / P1 | `RumocaCore/IR.lean`: DAE retains Flat, Solve retains DAE, and the artifact retains parsed tokens/AST plus Solve. Native generated constructors confirm some predecessors survive erasure. | Keep compact executable IRs and small provenance tables; express pass relations in `Prop`. Retain full stage dumps only when requested. Sharing is not deep copying, but it still prolongs object lifetimes. Source indices and proof fields erased by Lean should not be counted as resident copies. |
| PA08 / P1 | `Solve/Tensor.lean` uses inductive `Ref.here/there` and nested environment functions; the C algorithm's name environment follows the same pattern. Old-register lookup can traverse program depth repeatedly. Reverse AD saves pullback closures and updates through these references. | Refine typed references to bounded register indices and array-backed environments, with lookup/update and execution preservation. Measure old-register-heavy DAGs before adding operators. Preserve shape indices and operation counts independent of tensor volume; do not scalarize IR lowering. |
| PA09 / P2 | The original JSON failure handling constructed terminal diagnostics and then discarded them. The baseline 1 MiB error case cost 0.260 s / 218 MiB in CLI versus 0.041 s / 46 MiB in located parsing. `Diagnostics.renderAt` rebuilds file maps and physical lines. | Conditional terminal rendering is implemented and proved below. Sharing document line maps and bounding displayed terminal context remain open. Keep complete structured spans; prove byte/span conversions against the existing location contract if changed. LSP already stores a document file map. |
| PA10 / P2 | Actual artifact certificates, hashing and ZIP construction have separate materialization costs that this frontend benchmark does not measure. | Record emit, native compile, kernel certificate, hash and archive costs separately on each admitted slice. Reuse native Lake module caches; do not cache acceptance of changed external artifact bytes or weaken integrity checks. |

The measurements above predate the LALR source cutover and describe the
retired parser at revision the previous checkpoint.
They are historical evidence for the listed allocation and span-attachment
findings, not throughput measurements of the current parser. Production
Modelica and GALEC now both use the shared LALR engine; see
[the cutover evidence](lalr-parser.md#source-cutover-and-reusable-contracts).
Measure that implementation afresh before making a LALR, parol or ANTLR
performance comparison, and measure grammar generation separately from parsing.

One PA10 cache-selection issue is visible in `.github/workflows/ci.yml`: its
restore prefix hashes the entire root flake and lock file. Adding an optional
OMC environment therefore changes that prefix even when the verification
toolchain is unchanged. Ordinary source edits reuse the existing cache, but
this environment change starts a new CI cache bucket. A future key should
identify the actual verification environment, pinned Lean and dependencies;
do not use an unchecked fallback across incompatible toolchains. Upstream
mathlib proof download and the mandatory `--no-build` check remain in place.

A separate cancellation issue is repaired: pushes now preserve the active CI
run so it can save its checked native Lake cache. Only the newest pending
revision is retained. This changes workflow scheduling, not proof freshness,
the cache compatibility key or the full artifact gate.

The diagonal Jacobian development IR has a compact representation, but its
`eval` materializes a dense matrix. Dense output necessarily costs quadratic
space. Internal Jacobian-vector and vector-Jacobian products should preserve
operator structure rather than require that output. This is a representation
constraint for the current design, not permission to introduce general sparse
formats or new operators before their verified slice is ready.

An additional artifact-cost observation came from the required full gate for
this tooling change. At one sample, its `CheckEFMIArchive.lean` process had used
7 minutes 20 seconds of CPU time and held 7,559,044 KiB RSS (about 7.2 GiB).
The command and sample are retained in
`build/omc-probe/efmu-check-resource.txt`. These are a lower bound on that check's
total CPU time and a point-in-time RSS observation, not its eventual peak or
a repeated benchmark. The module proofs were already cached; this process
checks the actual fresh archive. PA10 therefore matters to development latency
as well as future artifact size. The default OMC comparison separately observed
about 39 seconds for checked FMU publication; that phase also includes the
native build and packaging, so it is not a pure certificate timing.

## Interning, sharing and incremental sessions

The Rust Rumoca checkout (HEAD `ab26a3984fd5bc5cd838b9b7e5619045f391f49f`,
with local changes) provides useful references: the inspected
`rumoca-core/src/ir_primitives/var_name.rs` uses compact IDs and shared
payloads; `spec/SPEC_0029_CRATE_BOUNDARIES.md` assigns shared identity/provenance
ownership; compilation sessions track dependencies and distinguish invalidation
causes. Its process-global `RwLock` interner is not a design to copy blindly:
putting a lock on every lexer occurrence would contend across Lean workers,
and a process-lifetime pool retains every historical LSP spelling.

Use file-local new-name collection with a shared immutable base and a controlled
merge. For a fresh batch, merge in stable file/occurrence order. Within an editor
workspace epoch, preserve old IDs and append new ones; **do not re-sort and
renumber the whole workspace after every edit**. Merge only changed files.
External output ordering and source maps must depend on stable source/declaration
identity, not incidental allocation order. Separate compilation/source snapshot
lifetimes from workspace spelling storage; reclaim by owned epochs, with a
proved remapping if compaction is later needed.

The proof obligations are exact spelling recovery, collision-safe lookup,
uniqueness, extension stability, token/AST decoding, name-resolution preservation
and deterministic parallel outcomes under the stated merge policy. Hashes are
indexes, never an axiom that different strings cannot collide. Reuse Lean/Std
map and array APIs and their existing lemmas rather than inventing a container.

Lean's [reference-counted runtime](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/)
and [arrays](https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/)
permit in-place updates when ownership is unique. Unintentionally retaining an
old array can force copying; cross-worker sharing also changes RC costs. The
pinned 4.29.1 runtime's ordinary array slots are machine words. An `Array UInt32`
is not automatically four bytes per entry on this 64-bit target; inspect the
concrete representation before promising a memory budget.

## What full MSL scaling will require

Loading a library and compiling one selected model are different operations.
A future session should read/index each definition once, share its source AST,
and instantiate only reachable classes. Scoped declaration IDs, dependency/SCC
analysis and instantiation overlays must avoid cloning the whole library for
each model. Cache keys will need the definition, scope, modifications and
structural parameters that actually affect semantics. Correct invalidation is
part of that design; Lake's proof cache does not cache Modelica model analysis.

MSL resolution, inheritance, instantiation, equation growth, AD scratch use,
whole-pipeline allocation counts, retained heaps and artifact certification
scaling remain unmeasured because the production grammar does not admit those
cases. Require these measurements at the relevant future slices. Do not grow
the grammar merely to create a benchmark, and do not claim MSL readiness from
a whitespace proxy.

After PA01, the immediate order is PA02/the remaining PA09 work and PA03/PA04, with package dependency
measurement alongside them. PA06–PA08 constrain the next verified representation
work before larger grammars/programs. Each semantic representation change needs
its refinement proof, existing axiom audit and full actual-artifact gate. The
performance findings do not replace unfinished FMI/eFMI obligations. Roadmap
E01 and E03 remain open; this report establishes the first baseline, not closure
of all performance budgets. Independent numerical comparisons with OMC are
specified in [docs/omc-comparison.md](../docs/omc-comparison.md).

The required full semantic/artifact gate passed for the initial tooling addition
in `build/omc-comparison-full-gate.log`. At that checkpoint, the targeted
performance command still failed on PA01; the original evidence remains in
`build/performance-audit/stack-reproduction/`.

## PA01 repair: exact attachment refinement

`Parser.Source.attachLoop` builds a reversed prefix and carries its alignment
continuation as an erased proof. It returns the recursive result directly and
reverses the completed prefix once. The generated native C uses a loop jump for
the token traversal; origin/input proof indices and the alignment continuation
are absent from the inner runtime arguments.

`Parser.LocatedProofs` supplies three audited theorems. `attachLoop_eq_reference`
relates every accumulator state to the reference cursor policy;
`attach_eq_reference` proves equality of the complete public result, including
failure; `lexLocated_eq_reference` lifts it to every located-lexer result,
including diagnostics. They quantify over arbitrary sources, trivia predicates,
tokens and valid starting positions, with no Modelica-specific assumption or
token-count bound. The direct recursive reference is noncomputable proof
specification, not an executable fallback. All three roots pass the unchanged
axiom whitelist in `build/span-attachment/audit.log`.

The 65,536-semicolon reproduction now produces the expected parse diagnostic in
all measured runs. Isolated located parsing took a median 0.031 s with about
29.3 MiB post-exec peak RSS. The rebuilt CLI took about 0.066 s at 1, 4 and 8
workers; its measured RSS was approximately 91 MiB. Raw data is retained in
`build/span-attachment/reproduction/` and `cli-reproduction/`. This repairs the
observed failure, not a claim that every frontend operation has a proved native
stack or memory bound. Lexer recursion, character-list allocation and the other
audit findings remain open.

One long-token input joins the existing native parallel-parser check, with an
inherited stack limit of at most 8 MiB. It checks the first extra token's exact
range and the same result in sequential and parallel batches; the 1,005-input
check passed in `build/span-attachment/native-boundary.log`. No new test suite
or grammar case was introduced. The required full
`nix develop .#verification --command lake test` gate passed for this repair in
`build/span-attachment/full-gate.log`, including the complete actual eFMU
certificate, source/C contracts, FMI ME/CS checks and mutation rejection. The
four hashed implementation/check files still matched the gate's starting
snapshot. PA01 is closed for the reproduced failure; the other performance
findings and the whole-compiler verification obligations remain open.

The retained FMU has SHA-256
`e633a5254fa71978e8030c7e6333ffb145aed6ea5ddf4476509479dc6e8e90d1`;
the eFMU has SHA-256
`8b00f150c3185a1ed6d3a6da55e2f37f15c14b9f9386ed5ad407ba77fd1812fe`.
The CI scheduling change passed `actionlint` in
`build/span-attachment/ci-lint.log`; hosted execution remains separately
visible in GitHub Actions.

## PA09 increment: render only the requested output

The CLI's pure `analyze` function now receives the terminal-output flag.
Its failure helper suspends terminal rendering behind `Unit → String` and
evaluates it only in terminal mode. JSON mode keeps the same structured
diagnostic and failure marker without building the discarded display text.
The generated native C branches before applying the rendering closure.

`Rumoca.ParseFilesProofs` relates the complete result to the former eager
implementation, kept as a noncomputable reference. Five audited roots prove
exact JSON, unchanged failure status, exact terminal output, and the same
ordered JSON array and aggregate exit flag for arbitrary parallel batch sizes,
worker counts and file-read snapshots. No source range, coordinate conversion
or parser/resolver decision changes. The proofs are separate from the runtime
imports and pass the compiler package audit in
`build/diagnostic-formatting/package-build.log`.

The rebuilt root CLI passes the existing 1,005-input sequential/parallel check
and LSP boundary checks in `build/diagnostic-formatting/frontend.log`. On the
same 1,048,629-byte lexical-error workload, three fresh-process runs with one
worker returned the expected diagnostic. Median wall time was 0.076 s and
median child peak RSS was 109,500 KiB (106.9 MiB). The preceding PA01 build's
paired baseline was 0.254 s and 225,896 KiB (220.6 MiB). Raw data and binary
identities are in `build/diagnostic-formatting/measured/` and
`build/pa09-preparation/before/`. These are host measurements, not proved
resource bounds or a claim about MSL throughput.

The full required `lake test` gate passed in
`build/diagnostic-formatting/full-gate.log`, including actual FMI/eFMI artifacts
and mutation controls. The source snapshot in
`build/diagnostic-formatting/source.sha256` still matches the checked files.
The remaining line-map and terminal-context work keeps PA09 open; identifier
interning, lexer allocation and bounded batch input retention are also open.
