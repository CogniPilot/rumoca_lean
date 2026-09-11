# Compiler performance audit — 2026-09-10

The current implementation is not ready for MSL-scale workloads. Identifier
interning is necessary, but the first measured release blocker is native stack
exhaustion in token-span attachment. The audit also finds avoidable whole-file
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
benchmark. It is outside `lake test`. Unexpected exits, including the currently
known stack overflow, make the command fail while retaining the evidence. Each
sample starts a fresh process after an unrecorded warmup; filesystem caches are
warm. Logs, workload files, raw samples, summaries and corpus inventories stay
under `build/`. No pass stamp or separate proof cache is introduced.

Baseline identity:

- Compiler revision: `c2dd147d93f329a7a341a35da82176e19d706ae5`; no compiler
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
semantic theorem. It needs implementation repair, not a larger stack setting.

## Findings and proof-preserving work order

| ID / priority | Evidence and consequence | Required change and closure evidence |
| --- | --- | --- |
| PA01 / P0 | `Parser/Located.lean`, `Source.attach` recurses through the remaining tokens before constructing the result. `parseLocated` attaches spans before syntax rejection. Isolated stage runs locate the observed stack overflow here. | Refine attachment to a tail-recursive accumulator or cursor. Prove identical success/error results, token spelling and span alignment; retain a native resource-boundary reproduction. Do not cap the accepted language or merely increase stack size. |
| PA02 / P1 | `ModelicaParser/Lexer.lean` expands the source into `List Char`, with additional identifier slicing; `Parser/Located.lean` scans gaps and spells tokens again. Generated native C confirms substring extraction and character-list allocation. | One UTF-8 cursor scan producing compact token IDs and exact byte ranges. Prove refinement to the lexical and location relations, including error offsets and Unicode boundaries. Stage allocation measurements must demonstrate the saving. The lexer also has non-tail per-token recursion; its larger-input limit is unmeasured, not the cause of the observed 65k crash. |
| PA03 / P1 | Identifier tokens and AST names carry `String`; no frontend interner exists. The C literal pool is unrelated. Passing one string into several records shares it, but repeated occurrences can still allocate distinct spellings. | Add compilation-owned spelling IDs with exact equality after hashing, reverse decoding and stable extension proofs. Keep spelling identity distinct from declaration identity and source occurrence. Measure retained memory and merge peaks, not only wall time. See the interning design below and roadmap E03. |
| PA04 / P1 | `Rumoca/ParseFiles.lean` reads every file sequentially before parsing. `Parser/Parallel.lean` partitions contiguous lists by file count, not bytes/cost. | Bound in-flight source bytes and results; overlap I/O with independent parsing. Preserve ordered outcomes, error spans and sequential equivalence. Use size-aware work distribution and explicit cancellation. A slow earliest result must not allow an unbounded reorder buffer. List partitioning allocates list spines, not copies of source bytes. |
| PA05 / P1 | Full CLI startup is about 70 MiB, versus 7.2 MiB for the isolated parser. `Rumoca.CLI` imports the FMI/eFMI driver and its broad runtime dependency closure. | Profile native initialization and dependencies; separate runtime definitions from proof-only modules where justified. Preserve mathematical libraries for proofs. This finding does not mean proofs are reverified per file; they are erased/cached as appropriate. |
| PA06 / P1 | Generic LALR reduction builds full trees, then checks their validity and token word; located LALR performs additional decoration. Candidate generation uses list item sets and linear searches through productions/states. | Measure generation separately from runtime. Index productions and canonical states; prove emitted tables retain their meaning. Refine runtime stacks/reduction actions to avoid redundant retained trees and checks only where a theorem discharges their purpose. Array action/goto tables and immutable grammar sharing are already good foundations. |
| PA07 / P1 | `RumocaCore/IR.lean`: DAE retains Flat, Solve retains DAE, and the artifact retains parsed tokens/AST plus Solve. Native generated constructors confirm some predecessors survive erasure. | Keep compact executable IRs and small provenance tables; express pass relations in `Prop`. Retain full stage dumps only when requested. Sharing is not deep copying, but it still prolongs object lifetimes. Source indices and proof fields erased by Lean should not be counted as resident copies. |
| PA08 / P1 | `Solve/Tensor.lean` uses inductive `Ref.here/there` and nested environment functions; the C algorithm's name environment follows the same pattern. Old-register lookup can traverse program depth repeatedly. Reverse AD saves pullback closures and updates through these references. | Refine typed references to bounded register indices and array-backed environments, with lookup/update and execution preservation. Measure old-register-heavy DAGs before adding operators. Preserve shape indices and operation counts independent of tensor volume; do not scalarize IR lowering. |
| PA09 / P2 | JSON failure handling constructs terminal diagnostics and then discards them. The 1 MiB error case costs 0.260 s / 218 MiB in CLI versus 0.041 s / 46 MiB in located parsing. `Diagnostics.renderAt` rebuilds file maps and physical lines. | Defer rendering to the selected output mode, share document line maps, and bound displayed context for very long lines while retaining complete structured spans. Prove byte/span conversions against the existing location contract if changed. LSP already stores a document file map. |
| PA10 / P2 | Actual artifact certificates, hashing and ZIP construction have separate materialization costs that this frontend benchmark does not measure. | Record emit, native compile, kernel certificate, hash and archive costs separately on each admitted slice. Reuse native Lake module caches; do not cache acceptance of changed external artifact bytes or weaken integrity checks. |

The production Modelica parser is currently the certified **DFA**, followed by
AST decoding, not the development generic LALR engine. Its current alphabet is
small (21 symbols plus the fallback encoding), with 91 states; encoding uses a
linear alphabet search. Do not present the measured DFA throughput as a LALR,
parol or ANTLR comparison. DFA grammar generation is also separate from parsing.

One PA10 cache-selection issue is visible in `.github/workflows/ci.yml`: its
restore prefix hashes the entire root flake and lock file. Adding an optional
OMC environment therefore changes that prefix even when the verification
toolchain is unchanged. Ordinary source edits reuse the existing cache, but
this environment change starts a new CI cache bucket. A future key should
identify the actual verification environment, pinned Lean and dependencies;
do not use an unchecked fallback across incompatible toolchains. Upstream
mathlib proof download and the mandatory `--no-build` check remain in place.

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

The immediate order is PA01, PA02/PA09 and PA03/PA04, with package dependency
measurement alongside them. PA06–PA08 constrain the next verified representation
work before larger grammars/programs. Each semantic representation change needs
its refinement proof, existing axiom audit and full actual-artifact gate. The
performance findings do not replace unfinished FMI/eFMI obligations. Roadmap
E01 and E03 remain open; this report establishes the first baseline, not closure
of all performance budgets. Independent numerical comparisons with OMC are
specified in [docs/omc-comparison.md](../docs/omc-comparison.md).

The required full semantic/artifact gate passed for this tooling addition in
`build/omc-comparison-full-gate.log`. The targeted performance command still
fails on PA01, retaining its stack-overflow evidence in
`build/performance-audit/stack-reproduction/`. A passing proof/artifact gate
does not close that separate native resource failure.
