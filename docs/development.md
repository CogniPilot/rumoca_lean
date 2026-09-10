# Incremental development

Enter `nix develop` once and run commands from the repository root. This keeps
all packages in one Lake workspace, sharing the pinned dependency builds.
`lake build` reuses unchanged `.olean` files; it does not re-elaborate every
module in the dependency graph shown by its job counter.

This is Lean/Lake's native proof reuse: Lean exports checked declarations to
`.olean` modules, and Lake hashes their source and build dependencies to decide
when to rebuild. Importing a cached module loads those declarations; it does not
rerun their tactics or recheck every imported proof in the kernel. The local
build artifacts are part of the normal Lean build trust boundary. See the
[Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

Prefer native Lake commands for daily Lean work, using the smallest applicable
target. For example, from this workspace:

```sh
lake build xml/XML xml/XMLChecks
lake build sha1/SHA1.CertificateProofs
```

The high-level targets below aggregate package-owned libraries through Lake's
native build graph. They reuse the same cached modules as direct package
targets. The Makefile has been removed.

| Command | Scope |
| --- | --- |
| `lake build check-parser` | Generic engine, grammar-parametric proofs and engine audits |
| `lake build check-modelica-parser check-galec-parser` | Language-owned grammar tables, AST actions and instance proofs |
| `lake build check-core` | Core IR/arithmetic proofs, tensor checks and core audits |
| `lake build check-c` | Shared C emission, numerical/memory/call semantics, printers and audits |
| `lake build check-fmi3` | FMI interface/lifecycle bodies and adapter audits |
| `lake build check-sha1` | Independent SHA-1 implementation, certificates, proofs and audits |
| `lake build check-xml` | Independent XML renderer, syntax proofs and audits |
| `lake build check-efmi` | eFMI library, Production C checks and backend audits |
| `lake build check-compiler` | Compiler composition proofs and compiler checks |
| `lake build sha1/SHA1.CertificateProofs` | One proof module using only Lean's standard library |
| `lake build rumoca_core/Tests.TensorChecks` | One package check module and its prerequisites |
| `lake build rumoca_compiler/rumoca` | Compiler CLI and its runtime prerequisites |
| `lake build audit` | All cached package check libraries |

Each package owns a separate check library and declares it as its `testDriver`.
`lake -d packages/core test`, for example, also works as a standalone package
check. Prefer the root commands during normal development: switching workspace
roots can select different dependency cache contexts. A backend check imports
its parser/core prerequisites, but no compiler-driver or unrelated sibling
checks. Changes to a prerequisite invalidate its dependent checks automatically.

The checks use `#audit axioms` from the small `verification` package. It audits
the exact declaration with Lean's `collectAxioms` and fails the build for any
dependency outside `propext`, `Classical.choice` and `Quot.sound`. Lake caches
that successful check using the same source/import traces as other Lean
modules. Replayed audit messages on a later build are cached diagnostics,
not another proof run. No hand-maintained "passed" stamp is used.

Lake can also check that these build products are current without rebuilding:

```sh
lake --no-build build sha1/SHA1Checks xml/XMLChecks proof_audit/ProofAuditChecks
```

It exits unsuccessfully if a target needs rebuilding. This inspects the native
package build cache; it does not replace the actual-artifact gate.

`lake build` builds the checked-in generated parser modules. Run `lake run generate`
explicitly after editing the EBNF; `lake run check-generated` checks freshness.
Avoid routine `lake update`, repeated mathlib cache extraction, or clearing
`.lake`: those are dependency-maintenance operations, not an editing loop.
Use `lake exe cache get` for initial setup or after an intentional dependency
change. Generated examples and logs stay under `build/`; deleting that directory
does not delete the package proof cache.

Once the change is ready, run the complete gate once:

```sh
mkdir -p build
nix develop .#verification --command lake test > build/verification.log 2>&1
```

This gate retains grammar freshness, actual-file certificates, mutation
rejection and native execution checks. Actual-file certificates still read the
current source, grammar and emitted files; they are not cached merely because
the checking entry point is unchanged. Package checks alone do not establish
the complete C/FMU/eFMU contract.

The full gate is the root package's native Lake test driver. Individual
integration stages are Lake scripts: `lake run verify-c`,
`lake run lalr-test`, `lake run fmi-test`, `lake run efmi-algorithm-test`, and
`lake run efmi-production-test`. `lake run demo` and `lake run fmu` retain the
example workflows. These scripts propagate failures and run their boundary
checks on each invocation; a passing stamp is never used to skip them.

The eFMI verification CLI first uses `lake build` to update its checking module
and imports, then runs the fixed actual-file entry point. `lake env lean` alone
only supplies an environment; it does not build imports. The native cache
reuses the checker implementation and library proofs. The file-specific
certificate is still constructed on each invocation.

The pinned eFMI schema contents have a separate `RumocaEFMIResources` library
with Lake's native `efmiSchemas` input-directory dependency. Its trace is binary,
so a line-ending change invalidates the embedded resource module.
`RumocaEFMISchemaCertificates` separately checks and caches each resource's
UTF-8 encoding, byte length and CRC-32. Model-specific archive checking reuses
those checked declarations; it still checks every actual archive byte against
them. A resource edit invalidates the dependent proof library through Lake.
The proof library and actual eFMI checker select Lean's 64 MB thread stack with
`-s 65536`; this is a resource option, not a trust-level or axiom change.

For frontend-only iteration, use `lake build check-modelica-parser check-lsp` and
`lake build rumoca-lsp`. `lake run frontend-test` runs one real stdio LSP
session and a native parallel parsing/file-adapter check. Batch parsing is
available through `lake exe rumoca parse --jobs 4 FILES...`; `--json` reports
structured ranges in input order. The ordinary error display includes source
context. These commands admit no additional Modelica syntax.

## GitHub CI

`.github/workflows/ci.yml` runs on pushes, pull requests and manual dispatch.
It first checks the generic engine and both language packages, then runs the
same required `nix develop .#verification --command lake test` gate. Logs and
produced FMUs are retained as workflow artifacts for 14 days, including failure
logs. Bash pipeline failure propagation prevents `tee` from hiding a failed gate.

The workflow pins actions to commit IDs and uses read-only repository permissions.
Nix supplies toolchains; Lake builds the source. One native cache retains
`.lake/packages`, `.lake/build` and `packages/*/.lake/build`, including checked
theorem modules and axiom-audit targets. Its compatibility prefix binds the OS,
architecture, Lean toolchain, Nix environment and dependency manifest. A commit
suffix lets each successful run save its incremental results, including newly
imported mathlib dependencies. Later commits restore the newest compatible cache
and still invoke every normal Lake target. Lake's source/import/build traces
decide what must be rebuilt, including changes to package configuration. There
are no cached "passed" stamps or separate proof-checksum schemes.

Only a complete cache miss downloads upstream artifacts for the directly imported
mathlib modules and their dependencies. The workflow checks `cache-matched-key`,
so restoring a previous commit also skips that download; `cache-hit` alone
would incorrectly treat that useful restore as a miss. See the
[cache restore action](https://github.com/actions/cache/tree/v5/restore).
The pinned Nix Lean uses `USE_GITHASH=OFF` and reports `v4.29.1` as its compiler
identity. Upstream mathlib artifacts have different native Lake traces, so a
cold build can rebuild those imports once. Re-extracting upstream archives over
a valid native cache would repeat that work. CI preserves the native artifacts
and does not separately retain the redundant compressed downloads.

Normal source edits therefore reuse unchanged mathlib and project modules;
changed modules and their dependents rebuild. A toolchain/dependency change or
[GitHub cache eviction](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching#usage-limits-and-eviction-policy)
can still require a cold build.

Imported `.olean` declarations are trusted compiled artifacts: their tactics and
kernel checking are not rerun merely because another module imports them.
Cache provenance and integrity therefore remain part of the build trust boundary;
Lake's freshness hashes are not signatures. These are GitHub Actions caches with
its normal branch/PR isolation, populated by successful workflow runs. A clean
rebuild is useful for checking reproducibility or investigating cache integrity,
but is not forced on every change.

The full `lake test` command still runs every time. Actual source/C/GALEC/XML/ZIP
certificates, mutation controls and native integration checks read fresh artifacts;
`build/` and their success status are never restored from the proof cache. Two
Lean workers limit memory contention without changing proof obligations.

Passing this workflow establishes the documented tiny-core gates. It does not
establish full Modelica/FMI/eFMI conformance, machine-code verification or DO-178C
compliance; the remaining obligations are tracked in `dev/`.
