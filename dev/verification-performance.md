# Verification build performance

Native Lake reuse covers both library proofs and actual-artifact certificates.
The full gate still runs artifact mutations, publication-failure checks and
native execution. Its success status is not cached.

## Initial measurement, 2026-09-16

The baseline revision `0bea31d` passed the full gate in 2790.9 seconds
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
| First 50, prior array pop | 528.8 s | ~9.17 GiB |
| First 50, masked pop | 220.7 s | ~6.84 GiB |
| All 99, masked pop | 548.7 s | ~8.08 GiB |

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
| Prior array pop | 88.1 s | ~6.47 GiB |
| Masked pop | 43.2 s | ~6.24 GiB |

`gotoMask` reduction alone costs about 0.1 s per distinct input, so the residual
per-certificate cost is the edge fold over the reduction symbols and the
state-length result vector, not the goto lookup. Progress credit validation
(`progress_checked`) is about 16 s in isolation and was left on its existing
`decide +kernel` route.
