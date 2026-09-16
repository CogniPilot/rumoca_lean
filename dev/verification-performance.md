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
