# Verification build performance

Native Lake reuse covers both library proofs and actual-artifact certificates.
The full gate still runs artifact mutations, publication-failure checks and
native execution. Its success status is not cached.

## Initial measurement, 2026-09-16

The baseline revision the previous checkpoint passed the full gate in 2790.9 seconds
(46.5 minutes). Its owning package proofs were already cached; repeated
file-specific certificates dominated the gate.

After adding native certificate build products, the same unit-profile FMI 3
source-build certificate measured:

| Operation | Wall time |
| --- | ---: |
| First certificate, with library imports already built | 566.537 s |
| Matching certificate, with Lake rebuilding disabled | 2.964 s |

That is approximately 191 times faster for the repeated certificate. These
timings cover the fixed source/C/adapter/XML/header checker, including Lake
startup and dependency checking. They do not include native C compilation,
archive creation or importer execution. The retained FMI certificate product
uses approximately 106 MiB, including the proof and exact input snapshots.

Evidence is in `build/artifact-cache/cold-fmi3-v3.json`,
`warm-fmi3-v3.json` and their stdout/stderr logs. The checked files were extracted
from the gate-produced `build/Integrator.fmu`, with the original source identity
`examples/Integrator.mo`. Reproduce inside the verification shell:

```sh
lake run verify-artifact fmi3 build/artifact-cache/prepared-fmi3 examples/Integrator.mo
lake run verify-artifact --check-only fmi3 build/artifact-cache/prepared-fmi3 examples/Integrator.mo
```

The cold command builds the certificate when absent; repeating it normally is
also cached. The no-build command succeeds only if all native prerequisites and
the certificate are reusable. Byte mismatches in retained input snapshots and
source identity were also rejected in no-build mode; restoring the snapshots
restored reuse. An exported C certificate imported into Lean and passed the
existing axiom audit. These are file/build boundary checks, not new semantic
theorems.

The required `nix develop .#verification --command lake test` passed on
2026-09-16 with these build products in place, in 36m16s, while a separate
build shared the machine. Every certificate was rebuilt cold in that run because
the root Lake file is a traced input and had changed; the steady-state warm
gate follows. Evidence is in `build/certificate-cache/full-gate-v3.log`.

The next full gate on the same revision, with every certificate reused, passed
in 11m57s (`build/certificate-cache/full-gate-v4-warm.log`), against the
46.5-minute baseline. The remaining time is Lake dependency checking, native C
compilation, importer runs, mutation rejections and the boundary scripts.

## Parallel axiom audits, 2026-09-19

The axiom audit for the heavier packages is partitioned into one audit file per
source module under a directory beside the check library's root
(`Tests/FMI3Audit/`, `Tests/FMI3CallPolicyAudit/`, `Tests/CAudit/`,
`Tests/CCallPolicyAudit/`, `Tests/TensorAudit/`, `Tests/Audit/`,
`Tests/FMI3SourceCallPolicyAudit/` and `Tests/CoreAudit/`). Each per-source file
imports only its own source module and the `ProofAudit.Audit` command, and holds
exactly the `#audit axioms` roots of that source module. The former root file
(for example `Tests/FMI3Audit.lean`) becomes a thin aggregator that imports every
per-source file, so the check library keeps its root name and its complete
audited-root set while Lake elaborates the audit as independent parallel jobs
instead of one serial module.

The previous single-file audits were each one serial Lake job on the critical
path of their check target; the largest, `Tests.FMI3Audit`, elaborated as one
job in about 381 seconds. Rebuilding only the audit files, with the package
sources cached, on a 32-core host now measures:

| Check target | Audit files rebuilt | Warm audit rebuild | Slowest single audit file |
| --- | ---: | ---: | --- |
| `check-core` | 56 | 13.5 s | `CoreAudit/RumocaCore_Initialization_Real`, 7.7 s |
| `check-c` | 234 | 36.3 s | `CAudit/RumocaC_InitializationMap`, 10.0 s |
| `check-fmi3` | 464 | 96.0 s | `FMI3Audit/ConstantFunctions`, 19.0 s |
| `check-compiler` | 132 | 42.2 s | `Audit/FMI3CSProtocol`, 19.0 s |

The audit-file count is the per-source files plus their aggregators. The warm
rebuild removes the audit build products and rebuilds the check target with the
package sources still cached, so it isolates audit elaboration. The critical path
of each target's audit is now its slowest single source-module file rather than
the whole audit, and the files fan out across available cores.

## Development loop

Use the smallest owning package/module build during proof development. Group
related work into a completed semantic obligation, then run the full gate once
before publishing that change. Repeating a full artifact gate for each helper
lemma does not improve the theorem and wastes time even with caching.

Changes to actual inputs, source identity, checker dependencies or the toolchain
invalidate their certificates. Without `SOURCE_DATE_EPOCH`, fresh eFMU UUIDs
and timestamps change XML, checksums and ZIP bytes and need new certificates.
Unchanged proofs are reused; a changed contract is never accepted through an
old result.

## Reusable eFMI certificates

The full gate checks two actual eFMI artifacts: the GALEC Algorithm Code in
`tests/efmi-algorithm.sh` and the complete Production eFMU in
`tests/efmi-production.sh`. Both stage their certificate inputs at stable paths
under `build/`, so the source identity string and every traced input byte
recur across runs. The Production eFMU compiles under a fixed
`SOURCE_DATE_EPOCH`, which selects reproducible RFC 9562 version 5 name-based
identities and a fixed generation time, so the archive bytes are identical
across runs. An unchanged actual-file certificate is then reused instead of
recomputed. No check is weakened: layout, UTC validity, distinctness, schema
conformance, checksum binding, native execution and every mutation rejection
still run against the actual bytes, and reuse under a different source identity
is rejected by a dedicated control.

Measured on 2026-09-16 with the compiler package already built and another
unrelated build sharing the machine:

| Run | `efmi-algorithm-test` and `efmi-production-test` wall time |
| --- | ---: |
| First run, both certificates built | 22m47s |
| Repeated run, both certificates reused | 5m18s |

The cold eFMU archive certificate dominates the first run. The repeated run
still executes every mutation rejection, each of which is a fresh, failing
certification attempt, plus native C compilation, extraction and schema checks.
Evidence is in `build/certificate-cache/efmi-reproducible-v1.log` and
`efmi-reproducible-warm-v1.log`.

See [the dependency and trust boundary](../docs/development.md#cached-artifact-certificates).

## Kernel-affordable checksum and tensor manifest certification

The tensor eFMI Production Code manifest is 7.4 KB (117 SHA-1 blocks), an order
of magnitude larger than the scalar manifests. Certifying it exposed two costs
in the checksum certificate that were negligible at the scalar sizes.

First, the SHA-1 compression function previously built its 80-word message
schedule with an array and an `Id.run` mutation loop, and worked over the
`Fin`-wrapped `UInt32` operations. The kernel reduces those poorly: one
`compress` step cost about 2.5 GiB, and 117 sequential per-block certificates
accumulated past 7.5 GiB. The schedule is now a plain structural list recurrence
(`blockWords`, `scheduleWord`, `extendSchedule`), and the working state and words
are masked `Nat` values below `2^32`, so the kernel uses its accelerated `Nat`
bitwise and arithmetic operations. The same 117 per-block certificates then cost
about 15 s and stay near 4 GiB. The digest value is unchanged; the FIPS 180-4
vectors still certify by kernel evaluation.

Second, a certificate over the whole 7.4 KB byte or character list overflows the
kernel's C reduction stack at the interpreter default thread stack. The fixed
checking entry points already run with a 64 MB thread stack (`lean -s 65536`, set
by the `verify-artifact` job), which is sufficient; no whole-content reduction is
weakened.

With both in place, the composed tensor manifest certificate
(`tensor-efmi-directory`: the three manifest documents' XML serialization and
validity, and the four SHA-1 code/manifest checksums, into
`Rumoca.CheckedTensorEFMIFiles.source_to_manifests`) certifies the actual bytes
within the shared gate's budget:

| Tensor manifest certificate (7.4 KB Production manifest), cold, `-s 65536` | Wall | Peak RSS |
| --- | ---: | ---: |
| Array/`Id.run` `UInt32` schedule (before) | did not finish | over 7.5 GiB (killed) |
| Structural masked-`Nat` schedule (after) | ~2.4 min | ~6.75 GiB |

Peak RSS was sampled by summing the process tree's resident set.

## XML serialization certificate: fragment cursor vs whole-document decide

The XML document certificate (`XML.CertificateCheck.certify`) previously reduced
the whole composed character list against a flat literal in one `decide +kernel`
step. Profiling that certificate on the 7.4 KB tensor Production manifest in
isolation (`lean -s 65536`, cold) attributed one kernel type-check of about 6.3 s
to that single whole-document decide, with the remaining time in bounded
per-element opening/closing decides (200 to 450 ms each) and the metaprogram that
builds the syntax. The whole-document decide is a large transient term that is
freed once checked; it is not the resident peak.

The certificate now decomposes each document into a pre-order list of per-element
character pieces, proved once and universally to flatten to the rendered document
(`XML.Certificate.pieces`, `render_pieces`, `documentPieces`, `document_pieces`),
certifies every element's opening and closing pieces against bounded literals by
reflexivity, and binds their concatenation to the actual bytes through a
block-structured cursor. No single kernel step reduces the whole document, so the
kernel work is linear in the document with a bounded per-fragment peak.

| Production manifest XML certificate, cold, `-s 65536` | Wall | Peak RSS | Dominant term |
| --- | ---: | ---: | --- |
| Whole-document `decide +kernel` (before) | ~41.7 s | ~5.42 GiB | one whole-document list-equality decide (transient) |
| Fragment cursor (after) | ~37.7 s | ~5.33 GiB | bounded per-fragment reflexivity + cursor splits |

For this document size the two are within noise on resident peak; the redesign
removes the super-linear whole-document decide so the cost stays linear as
documents grow. Composed into the tensor manifest certificate the two are also
within noise (6.75 GiB before, 6.90 GiB after).

## Tensor eFMU archive certificate

The complete tensor eFMU archive certificate (`tensor-efmi-archive`,
`Rumoca.CheckedTensorEFMIFiles.source_to_archive`) reads the actual `.efmu` bytes,
re-derives the manifest contract, and composes it with the stored-ZIP transport
over all fifty archive members. Measured cold, `-s 65536`, summing the process
tree's resident set:

| Archive certificate, cold | Wall | Peak RSS |
| --- | ---: | ---: |
| Scalar eFMU (`efmi-archive`, gated in `tests/efmi-production.sh`) | ~7.9 min | ~12.28 GiB |
| Tensor eFMU (`tensor-efmi-archive`) | ~8.5 min | ~12.79 GiB |

The tensor archive certificate peaks at parity with the scalar eFMU archive
certificate that the gate already builds and accepts. The resident peak is
dominated by accumulated declarations: the re-derived manifest contract (about
6.75 GiB on its own) plus the stored-ZIP payload certificates over all 140 KB of
archive members, roughly 130 KB of which are the pinned vendored schemas that the
scalar archive certificate also certifies. It is not dominated by any single
whole-document step, so reducing the XML serialization certificate does not lower
it materially; the earlier "8 GiB gate budget" figure was inconsistent with the
scalar archive certificate's actual cost and is withdrawn. The budget for the
tensor archive certificate is parity with the scalar archive certificate.

The certificate is gated through the default CLI publication in
`tests/tensor-c.sh` (next to the tensor manifest certificate) and
`tests/efmi-production.sh`, both under the fixed `SOURCE_DATE_EPOCH` and the same
tensor source identity, so it is built once and reused across the two scripts and
across gate runs. See [the tensor eFMU standards impact](standards-review.md).

## eFMU archive certificate: sharing the pinned payload certificates, 2026-09-19

The scalar `efmi-archive` and tensor `tensor-efmi-archive` certificates read the
actual `.efmu` bytes, re-derive the manifest contract, and compose it with the
stored-ZIP transport over all fifty members. The transport previously re-decided
every member's payload bytes block by block against that member's payload
certificate, so each archive re-certified roughly 130 KB of pinned vendored schema
payload, and each model-specific code payload twice (once building the payload
certificate in `certifyCRC`, once again in the transport). The pinned schema
payloads are already certified once as the Lake-cached
`Rumoca.EFMI.SchemaCertificates.resource_i.payload` products.

The transport (`StoredZIP.ArchiveCertificateCheck.certifyCore`) now consumes each
member's payload certificate by name instead of re-deciding it: it reads the
actual payload region, confirms at check time that it equals the certified bytes
(`actualPayload == item.text.toUTF8`), and builds the local record from the
certified `Certificate.Text` fields (`bytes`, `encoding`, `length`, `checksum`)
directly. Identity with the actual file is established by the checker reading the
archive bytes and comparing them, never by trusting an earlier run. The
`StoredZIP.Format.Conforms` and `source_to_archive` statements are unchanged; only
the proof route changed.

Measured cold with a /proc process-tree resident poller sampling every 0.2 s, on
the fixtures the scripts produce (the scalar eFMU compiled under the fixed
`SOURCE_DATE_EPOCH`, the tensor eFMU via the tensor path), reported both as the
whole `lake run verify-artifact` process-tree sum and as the pure certificate
(lean) process. A shared full gate was running on the machine, so wall figures
carry CPU-contention noise; the per-tree resident peak is unaffected by other
processes:

| Archive certificate, cold | Wall | Peak (process tree) | Peak (lean process) |
| --- | ---: | ---: | ---: |
| Scalar `efmi-archive`, before | 502 s | 12.19 GiB | - |
| Scalar `efmi-archive`, after | ~340 s | 8.95 GiB | 7.32 GiB |
| Tensor `tensor-efmi-archive`, before | 513 s | 13.27 GiB | - |
| Tensor `tensor-efmi-archive`, after | ~340 s | 8.15 GiB | 6.52 GiB |

The whole-tree sum includes the `lake` orchestrator process (about 1.6 GiB); the
previously documented pre-change baselines (12.28 GiB scalar, 12.79 GiB tensor)
match the before rows. Measured as the docs' pure-lean certificate process, the
post-change certificate peaks well under 8 GiB.

Attribution, by bounded probe: the manifest-only `efmi-directory` certificate for
the same scalar fixture peaks at 8.74 GiB (tree) on its own in 197 s. The
post-change archive certificate sits at parity with it, so the payload sharing
removed essentially all of the stored-ZIP contribution to the peak; what remains
is the manifest contract re-derivation plus the fixed cost of loading the compiler
proof chain that every one of these certificates pays. The archive still
re-derives `source_to_manifests` in its own process because the `efmi-directory`
and `efmi-archive` kinds are separate certificate products with no shared olean;
sharing that derivation across the two products would need a
certificate-infrastructure change and would not lower the peak below the manifest
floor. The certificate wall (cold, via `lake run`) is about 5.6 min scalar and
5.5 min tensor, down from 8.4 and 8.6 min; a large fixed fraction is Lake
dependency replay and the shared manifest re-derivation, not the stored-ZIP work.

## LALR reduction certificate reformulation, 2026-09-19

The generated LALR tables prove one reduction summary per grammar production.
Each such `reduction_N_checked` certificate previously reduced `Safety.popStates`
directly: an `Array.ofFn` over the states with an inner `edges.all`, re-expanded
at every reduction symbol, which the kernel walks as a list with per-index cost.
The certificates now rewrite through the bitmask reformulation in
`Parser.LALR.MaskedSafety` (`popStates_eq`, `gotoMask_eq`) and let the kernel
reduce a `Nat`-bitmask fold with machine-word bit operations. Statements and
certified conditions are unchanged.

Measured with `lake env lean -s 65536`, summing the process tree's resident set.
The Modelica module `ModelicaParser.Generated` (222 LALR states, 99 reduction
certificates) is measured by group, since the whole module exceeds a single
measurement window:

| Modelica reduction certificates | Wall | Peak RSS |
| --- | ---: | ---: |
| First 50, prior array pop | 528.8 s | ~8.75 GiB |
| First 50, masked pop | 220.7 s | ~6.52 GiB |
| All 99, masked pop | 548.7 s | ~7.71 GiB |

The prior all-99 reduction group was previously profiled near 980 s; the masked
all-99 group now costs less than the prior route spends on its first 50. The
whole changed safety region (shared premises, all reduction certificates, and the
`reductions_checked`/`acceptance_checked`/`safety_checked` aggregation) checks
green together in 591 s; its resident peak is set by the unchanged whole-table
`safety_checked` decision, not by the reductions.

The GALEC module `GALECParser.Generated` (117 LALR states, 11 reduction
certificates) is small enough to measure whole:

| GALEC module | Wall | Peak RSS |
| --- | ---: | ---: |
| Prior array pop | 88.1 s | ~6.17 GiB |
| Masked pop | 43.2 s | ~5.95 GiB |

`gotoMask` reduction alone costs about 0.1 s per distinct input, so the residual
per-certificate cost is the edge fold over the reduction symbols and the
state-length result vector, not the goto lookup. Progress credit validation
(`progress_checked`) is about 16 s in isolation and was left on its existing
`decide +kernel` route.

## LALR per-row safety certificates, 2026-09-19

The generated tables previously closed the whole-table structural-safety
obligation with a single `safety_checked` decision: after rewriting the
reduction and acceptance summaries to literal arrays, one `decide +kernel`
reduced `Safety.TableConditions` over every state and symbol at once. That
predicate reads the literal reduction/acceptance vectors, which the kernel
represents as lists, so a lookup at state `q` costs `O(q)` and the whole
decision grows about `states^2 x symbols`. On the 222-state Modelica table it
was the module's largest single transient.

`Parser.LALR.RowSafety` isolates the obligation of one state into `rowValid`,
reading only that state's already-extracted action and goto rows.
`safety_of_rows` proves the whole-table `TableConditions` equivalent to the four
grammar/table prefix conditions plus `rowValid` at every state, through
`entryRowOK_iff`/`gotoRowOK_iff` (which relate the row lookups to the table
lookups via `action_eq_row`/`goto_eq_row`). The generator emits one certificate
per fixed-size chunk of states and joins them through `safety_of_rows`, so no
single kernel term covers the whole table. The `safety_checked` statement and
the certified `Safety.validate ... = true` conclusion are byte-identical; only
the proof route changed.

Measured with `lake env lean -s 65536`, summing the process tree's resident set,
over the isolated safety obligation for the 222-state Modelica table (the same
literal reduction/acceptance arrays feed each variant):

| Modelica safety obligation | Wall | Peak RSS |
| --- | ---: | ---: |
| Prior whole-table `TableConditions` decision | 156 s | ~18.76 GiB |
| Per-state rows, one certificate per state (222) | 110 s | ~14.15 GiB |
| Per-state rows, one certificate per 10 states (23) | 108 s | ~6.82 GiB |

Chunking amortizes the per-certificate decision term that the elaborator retains
across the module, so the ten-state chunk brings the isolated safety obligation
under 8 GiB and below the reduction group's ~7.71 GiB peak, while individual
per-state certificates stay dominated by that retained-term growth. The chunk
size of ten is used by the generator.

Once the whole-table safety transient is gone, the module's resident peak is set
by the cumulative retention of the per-state certificates the elaborator keeps in
one process: the 99 reduction certificates and the 222 item certificates. The
item certificates use the same per-state `decide +kernel` pattern, so they were
chunked the same way (`itemCertificates`, ten states per certificate joined
through `ItemCheck.validate_iff`). Isolated on the 222-state Modelica table:

| Modelica item obligation | Wall | Peak RSS |
| --- | ---: | ---: |
| One certificate per state (222) | 107 s | ~11.48 GiB |
| One certificate per 10 states (23) | 85 s | ~7.05 GiB |

The whole `ModelicaParser.Generated` module still exceeds a single measurement
window (its wall is set by the 99 reduction certificates), and its resident peak
remains set by the cumulative retention of the reduction and now-chunked item and
row certificates rather than a single whole-table transient; a partial cold build
of the pre-item-chunk state reached about 22.7 GiB, against about 24 GiB for the
prior whole-table route. Bringing the whole module under 8 GiB would require
splitting the certificates across modules so each process reclaims independently,
or chunking the reduction certificates; both are separate from the safety
obligation. The `GALECParser.Generated` module (117 states) checks whole in 49 s;
its peak moves from ~5.95 GiB on the prior route to ~7.18 GiB with per-row safety
alone and back to ~6.44 GiB once the item certificates are also chunked. At that
smaller scale the per-chunk certificates are a small net change, still under
8 GiB.

## Cold gate hot-spot inventory, 2026-09-19

Measured from the cold full-gate log in which the LALR tables rebuilt cold
(`ModelicaParser.Generated` at 456 s). Per-module figures are single-module
cold elaboration wall times from the `Built X (N s)` lines; certificate peak
resident sets are the `-s 65536` process-tree sums recorded above.

| Hot spot | Cold wall | Peak RSS | Scales with |
| --- | --: | --: | --- |
| ModelicaParser.Generated (LALR tables, 222 states) | 456 s | ~22.7 GiB (cumulative reduction + item + row certificates) | states x symbols, superlinear |
| Tests.FMI3Audit (~2312 roots, one serial module) | 367 s | n/a | roots x profiles, serial |
| RumocaC.PrinterProofs | 165 s | n/a | printer proof size |
| Tests.Audit | 136 s | n/a | roots |
| RumocaFMI3.TensorStorageCode | 96 s | n/a | tensor extents |
| RumocaFMI3.LiteralPreparation | 93 s | n/a | adapter functions |
| RumocaFMI3.StepArguments | 88 s | n/a | adapter functions |
| LALR reductions, all 99, masked pop | 548.7 s | ~7.71 GiB | productions x states |
| FMI 3 source-build certificate (unit) | 566.5 s / 2.96 s warm | ~106 MiB product | adapter bytes |
| Tensor eFMU archive certificate | ~8.5 min | ~12.79 GiB | archive bytes |
| Scalar eFMU archive certificate | ~7.9 min | ~12.28 GiB | archive bytes |
| Tensor manifest certificate (7.4 KB) | ~2.4 min | ~6.75 GiB | manifest blocks |
| XML document certificate (fragment cursor) | ~37.7 s | ~5.33 GiB | document bytes |
| SHA-1 checksum, 117 blocks, masked-Nat | ~15 s | ~4 GiB | blocks |

Audit modules, each a single serial Lake job: FMI3Audit 367 s, Audit 136 s,
CAudit 56 s, FMI3CallPolicyAudit 47 s, CoreAudit 33 s, TensorAudit 24 s.

Per-profile proof-family cold elaboration: the tensor family is 30 modules and
467 s; the constant family is 10 modules and 130 s. `TensorDoStep` (48 s),
`ConstantDoStep` (27 s) and the base DoStep are one proof template instantiated
per profile.

## LALR certificate module split, 2026-09-19

The generated certificates are split across a directory of modules per grammar
(see [lalr-parser.md](lalr-parser.md#generated-certificate-module-layout-2026-09-19)).
Each obligation group elaborates in its own Lean process, so the kernel decision
terms are reclaimed per module instead of accumulating in one process, and Lake
builds the independent groups in parallel. The final theorem names, statements
and audited axioms are unchanged.

Per-module peak resident set is the GNU `time -v` maximum resident set size of
`lake env lean -s 65536` compiling that one module with its dependencies already
built. Each module is a single lean process, so the maximum resident set is the
module's own peak. The Modelica `ModelicaParser.Generated` prefix (222 LALR
states, 99 reduction certificates) measures, in isolation:

| Modelica module | Wall | Peak RSS |
| --- | ---: | ---: |
| Generated/Tables | 39.2 s | ~4.21 GiB |
| Generated/Source | 31.7 s | ~5.80 GiB |
| Generated/Items | 76.7 s | ~5.47 GiB |
| Generated/Reductions0 (20) | 81.6 s | ~4.07 GiB |
| Generated/Reductions1 (20) | 83.1 s | ~4.41 GiB |
| Generated/Reductions2 (20) | 84.2 s | ~4.22 GiB |
| Generated/Reductions3 (20) | 89.6 s | ~4.14 GiB |
| Generated/Reductions4 (19) | 80.9 s | ~4.03 GiB |
| Generated/Safety | 93.0 s | ~4.98 GiB |
| Generated/Progress | 7.8 s | ~2.80 GiB |
| Generated (umbrella) | 3.8 s | ~1.85 GiB |

No module exceeds 8 GiB; the largest is `Generated/Source` at ~5.80 GiB, against
the prior single module's cumulative ~22.7 GiB. The reduction certificates that
alone summed to ~7.71 GiB now sit in five modules of ~4 GiB each, and the row and
item chunks that peaked at ~6.82 GiB and ~7.05 GiB are in their own processes.

The whole target built clean with Lake parallelism (default job count on the
32-core host; this Lake exposes no job-count flag) from removed generated oleans:

| Whole target, clean parallel build | Wall |
| --- | ---: |
| `modelica_parser/ModelicaParser.Generated` | 272 s |
| `galec_parser/GALECParser.Generated` | 36 s |

The Modelica target is 4 m 32 s, under the five-minute goal, against the prior
monolith whose wall was set by the 99 reduction certificates in one process and
exceeded ten minutes (the cold gate recorded it at 456 s). In the parallel run
`Generated/Tables` builds first (71 s, a dependency of every other module); the
independent groups then run together (`Generated/Progress` 13 s, `Generated/Source`
48 s, `Generated/Items` 101 s, the five reduction modules 96 to 104 s), and
`Generated/Safety` (91 s) starts once its reduction dependencies finish and
completes the target. Contended per-module walls run a little longer than the
isolated numbers above.

The GALEC `GALECParser.Generated` prefix (117 LALR states, 11 reduction
certificates) is small; every module stays under ~3.1 GiB (largest
`Generated/Safety` ~3.07 GiB) and the whole target builds in 36 s.

## Profile-generic adapter render plan, 2026-09-19

The base scalar, tensor and constant FMI 3 adapters share one render plan and one
render-identity proof family (see
[fmi3/contracts.md](fmi3/contracts.md#profile-generic-render-plan)). The
five-piece renderer identity, the located-fragment facts and the byte-for-byte
character-identity lemma are now proved once over an arbitrary `RenderPlan`; each
profile supplies a plan value and its render-identity theorems and adapter-bytes
character lemma become corollaries. Two duplicated helper lemmas (the per-profile
`function_chunks`) and three copies of each render-identity proof are removed.

Per-module cold elaboration (Lake's reported per-module seconds, dependencies
already built, module oleans removed and rebuilt) before and after the shared
plan:

| Module | Before | After |
| --- | ---: | ---: |
| `RumocaFMI3.AdapterRenderPlan` (new) | n/a | 1.1 s |
| `RumocaFMI3.TensorFunctions` | 4.6 s | 2.5 s |
| `RumocaFMI3.ConstantFunctions` | 4.5 s | 2.5 s |
| `Rumoca.FMI3AdapterProofs` | 2.6 s | 2.6 s |
| `Rumoca.TensorAdapterChars` | 2.1 s | 2.1 s |
| `Rumoca.ConstantAdapterChars` | 2.1 s | 2.1 s |

The two per-profile function modules each drop about two seconds because their
renderer, member and helper identities are single generic corollaries instead of
three separate rewriting proofs. The character-identity modules are unchanged in
cost. The added generic module is about one second, so the touched-module total
falls even with the new module included. The three profiles' `source_to_build`
adapter certificates still produce with identical statements and depend only on
`propext`, `Quot.sound` and `Classical.choice`, confirmed by running
`verify-artifact` for the `fmi3`, `tensor-fmi3` and `constant-fmi3` kinds over
the actual extracted FMU sources, and the tensor and constant adapter
standalone-object boundary checks in `tests/tensor-c.sh` still pass.


## Profile-generic Float64 value-reference dispatch, 2026-09-19

The tensor and constant-rate `fmi3GetFloat64` / `fmi3SetFloat64` bodies share one
value-reference dispatch shape (see
[fmi3/contracts.md](fmi3/contracts.md#profile-generic-float64-value-reference-dispatch)).
The printability of that dispatch is now proved once, by induction over the
reference list, in `RumocaFMI3.Float64Dispatch`, and the printability of the
getter and setter body around an abstract dispatch is proved once in
`RumocaFMI3.TensorFloat64Access`. Each profile obtains the printed-text
denotation of its accessors by instantiating those shared results at its own
reference list, instead of re-walking the whole body under a raised heartbeat
budget. The two `set_option maxHeartbeats 4000000` printability reproofs that the
constant-rate accessor carried are removed; the equivalent shared proofs run once
and are cited by both profiles.

Per-module cold elaboration (Lake's reported per-module seconds, dependencies
already built, module oleans removed and rebuilt) before and after:

| Module | Before | After |
| --- | ---: | ---: |
| `RumocaFMI3.Float64Dispatch` (new) | n/a | 1.7 s |
| `RumocaFMI3.TensorFloat64Access` | 23 s | 20 s |
| `RumocaFMI3.ConstantFloat64Access` | 15 s | 3.1 s |

The constant-rate accessor drops from about fifteen seconds to about three because
its two raised-budget printability reproofs are replaced by citation of the
shared proofs; its dispatch printability is a short induction over the reference
list. The tensor accessor drops a few seconds as the value-reference printability
moves off its per-profile path; the remainder is intrinsic behavioral machine-
execution semantics that stays per profile. The decisive effect is that the
value-reference printability no longer scales per profile: a further profile that
fits this accessor shape pays the small constant-rate-like cost, not a fresh
body-length reproof. `ConstantFloat64.get_contract` and `set_contract` keep their
statements and depend only on `propext`, `Quot.sound` and `Classical.choice`;
the three `verify-artifact` certificate kinds and the two adapter standalone-object
boundary checks continue to pass.
