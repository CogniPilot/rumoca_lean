# Rumoca compiler package

This package composes parsing, Flat/DAE/Solve lowering and the C backend. It owns
the compiler driver, source semantics, cross-stage contracts, whole-compiler
theorem and actual-file checker. It depends on the other packages; they do not
depend on it.

Use `lake build check-compiler` from the repository root for incremental composition
proofs and axiom checks. `RumocaCompilerChecks` is the package's `lake test`
library. Parser, core and target audits live in their owning packages; compiler
checks cover the composed contracts. See
[development commands](../../docs/development.md).

| Location | Responsibility |
| --- | --- |
| `Rumoca/Compiler.lean` | Source-bound compilation driver and output artifact |
| `Rumoca/Provenance.lean`, `Initialization.lean`, `InitializationDiagnosticProofs.lean` | Exact input identity, source-to-Solve initialization and declaration-based compiler/editor notices |
| `Rumoca/ArrayCompiler.lean`, `ArrayProofs.lean` | Development array preparation, located source binding and complete Real equation/initialization preservation through stored Solve IR |
| `Rumoca/FMU.lean` | Staged FMU build, actual-kernel checker invocation and atomic publication |
| `Rumoca/GALEC.lean`, `EFMIProofs.lean` | DAE/GALEC/Solve algorithm composition and Algorithm Code artifact contract |
| `Rumoca/EFMIExport.lean` | Candidate identities, staged `.alg`/`.efmu` checking and atomic publication |
| `Rumoca/EFMIArchive.lean`, `EFMIArchiveProofs.lean` | Pure archive preparation and source-to-archive preservation theorem |
| `Rumoca/EFMIInitializationProofs.lean` | Actual Production C Startup result, completed source initialization and exact-archive consequence |
| `Rumoca/EFMIArtifactCheck.lean`, `EFMIArchiveArtifactCheck.lean`, `Tools/CheckEFMI*.lean` | Fixed actual-file checkers for Algorithm Code, Production Code, manifests and complete archives |
| `Rumoca/Source.lean` | Source Real and sampled semantics, with no backend import |
| `Rumoca/Semantics.lean`, `Lowering.lean`, `Behavioral.lean` | IR semantics, pass composition and numerical refinement |
| `Rumoca/Verified.lean` | Whole-compiler behavior preservation and artifact contract |
| `Rumoca/ArtifactCheck.lean`, `Tools/CheckArtifact.lean` | Trusted actual-file checking adapter and fixed entry point |
| `Rumoca/CLI.lean`, `Main.lean`, `Certify.lean` | Declarative CLI using lean4-cli, entry point and untrusted candidate-certificate generator |
| `Rumoca/ParseFiles.lean`, `ParseFilesProofs.lean` | Parallel file analysis; exact JSON, terminal-output and failure-status preservation while skipping unused terminal rendering |
| `Rumoca/EFMICheck.lean`, `EFMICheckOptions.lean` | Explicit process arguments and one snapshot of the actual eFMI source/code inputs |
| `Tests/` | Compiler regressions, semantic counterexamples and proof-root audit |

`compile` accepts a `Parser.Source.InputRef`: a checked entry in the caller's
immutable input table. Artifacts retain that identity through the scalar
Flat/DAE/Solve origin chain. FMI/eFMI publication takes the artifact and output
path, using the artifact's source snapshot. It cannot receive a second,
potentially different source string.

Actual-file certificates are cached as checked `.olean` products by the root's
`lake run verify-artifact` build job. The job tracks input bytes and checker
dependencies; publication preserves the original source identity across staging
directories. Native checks still run, and fresh eFMU metadata requires a fresh
certificate. See [certificate reuse](../../docs/development.md#cached-artifact-certificates).

The C target machinery is shared by both output routes:
DAE → GALEC → Solve → C for eFMI, and DAE → Solve → C for FMI 3.
GALEC text is rendered from the same checked GALEC product that is refined
into Solve. Compiler composition binds both eFMI code members to that common
origin. C emission itself only consumes prepared Solve programs.

`Rumoca.ArrayCompiler.prepare` is the development array entry point. Its result
retains the located parse and a stored executable tensor IVP with its lowering
certificate. `prepare_correct` composes lexical/EBNF binding with the Real
equation, initialization and Jacobian contracts. The two examples in
`examples/development/` exercise this path in the existing native checks.
Production CLI generation still rejects them until their finite C and actual
FMU/eFMU contracts are complete.

Module imports remain `Rumoca.*` and theorem names are unchanged. The public
`Rumoca` module includes proofs; the compiler executable imports only runtime
modules through `Rumoca.CLI`. Artifact output uses the fixed proof checker as a
separate process and requires the workspace (found from the current directory,
executable path, or `RUMOCA_ROOT`) and its built proof modules.

```sh
# From the repository root, inside nix develop:
lake build                        # delegates to this package's default targets
lake build rumoca_compiler         # explicit equivalent
lake exe rumoca examples/Integrator.mo
lake exe rumoca examples/Integrator.mo -o build/Integrator.fmu
lake exe rumoca examples/Integrator.mo -o build/Integrator.alg
lake exe rumoca examples/Integrator.mo -o build/Integrator.efmu
lake exe rumoca verify-algorithm build/Integrator.alg --source examples/Integrator.mo
lake exe rumoca verify-efmi build/Integrator.efmu --source examples/Integrator.mo
lake exe rumoca verify-efmi --help

# Standalone package build, using its own pinned manifest:
lake -d packages/compiler build
```

Executables are in `packages/compiler/.lake/build/bin/`. Run the complete gate
from the repository root with `lake test`; a package build alone does not run
the cross-package artifact and native execution checks. The checker defaults
to `packages/modelica-parser/grammar/Modelica.ebnf` relative to the repository root.
Call it through `scripts/verify-artifact.sh`, or supply `RUMOCA_GRAMMAR` when
using the checking entry point from another directory.

`verify-efmi` takes a complete **archive**, or the root of a prepared directory containing
`__content.xml`, `AlgorithmCode/manifest.xml`, `AlgorithmCode/model.alg`,
`ProductionCode/manifest.xml` and `ProductionCode/production.c`. The checker
reads candidate IDs and the generation timestamp from the manifests and
requires their complete bytes to match the correlated products. This is the
frozen emitted layout, not an importer for arbitrary eFMI directory layouts.
The fixed theorem also requires valid brace-delimited UUIDs, pairwise distinct
after case normalization, and a checked Gregorian UTC timestamp at whole seconds.
The original Modelica file is explicit because it need not be in an eFMU.
All three manifest names must match that file's parsed model name. The fixed
certificate binds the name to the parsed AST and the actual XML syntax trees;
renaming the source requires regenerating its correlated manifests.
Both check commands default to the workspace's EBNFs; `--grammar` and
`--galec-grammar` allow explicit overrides for auditing another actual file.
Paths are resolved before switching to the workspace. No eFMI input or identity
environment variables are used. Archive checking additionally certifies every
ZIP record and the exact five code/XML members plus all 45 pinned schema
resources. Its fixed `source_to_archive` theorem includes the same compiler,
code, execution and manifest contracts. Directory checking covers the code/XML
snapshot without claiming an archive certificate.

The `.alg` path checks the actual Modelica source, Algorithm Code and both EBNF
files before publication. The `.efmu` path uses `Artifact.efmuArchive`, whose
successful results satisfy `compile_archive_verified`, then checks the actual
staged archive before a same-filesystem rename. Candidate UUIDs and the UTC
timestamp use Lean's standard system APIs; the kernel checks their emitted
identity profile. Entropy quality, global uniqueness, clock accuracy and file
publication remain external infrastructure. The CLI needs no identity flags,
environment variables or external UUID/date program. Audit output goes to
stdout and archive publication progress goes to stderr.

These are the frozen tiny profile's contracts, not complete eFMI standards
conformance. See [the eFMI standard review and gates](../../dev/efmi.md).

`rumoca parse --jobs 4 FILES...` parses and checks independent tiny Modelica
files in parallel, retaining argument order and per-file diagnostics. It reads
files once before parallel analysis; cross-file name resolution is not added.
Use `--json` for structured UTF-8 spans, or the default source-context display.
The separate [LSP package](../lsp/README.md) uses the same structured parser
errors with editor ranges.
