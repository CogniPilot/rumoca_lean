# Repository organization

All compiler implementation and proof code lives in Lake packages. The root
coordinates builds, development tools, examples and cross-package checks.

```text
packages/
  verification/
    ProofAudit/               Shared build-time axiom audit command (Lean only)
  sha1/
    SHA1/                     Independent SHA-1 implementation and certificates
    Tests/                    SHA-1 proof audits and existing standard vectors
  xml/
    XML/                      Independent XML renderer, syntax and proofs
    Tests/                    XML proof audits
  parser/
    Parser/                  Generic EBNF, scanner, DFA/LALR runtime, spans and proofs
    Generate.lean            Grammar-parametric DFA generator
    LALRGenerate.lean        Grammar-parametric LALR candidate generator
    Tests/                   Engine-only proof audits and kernel regressions
  modelica-parser/
    grammar/                 Selected Modelica EBNF and restrictions
    ModelicaParser/          Generated tables, lexer, AST, actions and proofs
    Tests/                   Modelica parser, location and parallel-result audits
  galec-parser/
    grammar/                 Selected GALEC EBNF and restrictions
    GALECParser/             Generated tables, scanner policy, syntax and proofs
    Tests/                   GALEC instance audits
  core/
    RumocaCore/               Flat/DAE/Solve IR, arithmetic and transition proofs
    Tests/                    Core theorem audit and tensor checks
  backend-c/
    RumocaC/                  Shared Solve → C emission, printers and target semantics
    Tests/                    Shared numerical, memory, call and printer proof audits
  backend-fmi3/
    RumocaFMI3/               FMI interfaces, adapter/time proofs, metadata and packaging
    vendor/fmi3/              Pinned official FMI headers and license
    Tests/                    FMI generated-body proofs and audits
  backend-efmi/
    RumocaEFMI/               GALEC rendering, Solve → Production C and target proofs
    RumocaEFMIResources.lean  Pinned schema contents, with Lake input-directory tracking
    RumocaEFMISchemaCertificates.lean  Separately cached encoding and CRC proofs
    Tests/                    Production C execution and artifact regressions
  compiler/
    Rumoca/                   Driver, source semantics and composed correctness
    Main.lean, Certify.lean    Executable entry points
    Tools/                    Fixed actual-artifact checking entry points
    Tests/                    Compiler regressions and axiom audits
  fmu-runner/
    FMURunner.lean            Independent Lean CLI around FMPy
    Main.lean                 Runner executable entry point
  lsp/
    RumocaLSP/                Immutable editor snapshots and Lean-based LSP transport
    Main.lean, Tests/         Stdio server and package-local proof audit
tests/                        Repository integration and adversarial checks
scripts/                      Reusable artifact-verification and audit commands
examples/                     Modelica example and tested C host
nix/                          Packaged editor, configuration and LSP check
docs/                         Current contracts and design references
dev/                          Compiler review and authoritative roadmap
```

Every package has a `lakefile.toml`, dependency manifest, toolchain pin and
README. Import names (`ModelicaParser.*`, `RumocaCore.*`, `RumocaC.*`, `Rumoca.*`)
identify package ownership. Reusable utility packages use independent Lake
names (`sha1`, `xml`, `proof_audit`) and module/namespace roots (`SHA1`, `XML`,
`ProofAudit`). Their public APIs do not require a `Rumoca` namespace.
Compiler IRs, language definitions and backends retain Rumoca names.

The `parser` package uses the independent `Parser` module and namespace root.
It contains no language grammar, AST, keyword list or language import. The
`modelica_parser` and `galec_parser` packages depend on that engine; neither
frontend depends on the other. Their language APIs retain `Rumoca` namespaces,
while their module roots (`ModelicaParser`, `GALECParser`) identify ownership.
This is a dependency separation, with no compatibility modules.

Check libraries depend on the independent verification tooling package; runtime
modules do not import it. SHA-1 uses only Lean's standard library; its own check
library uses verification tooling. Both the eFMI backend and the compiler's
manifest checker explicitly depend on this independent package.
XML rendering, syntax and proofs also use only the standard library and have
their own checks. Both FMI backends and the compiler's manifest checker depend
on XML; model-specific document construction remains in the backends.
The compiler also depends on both language frontends, core, backend-c, backend-fmi3 and
backend-efmi. The runner uses only Std and the external FMPy executable. Core
uses the source AST. Both FMI backends use backend-c; neither depends on the
other. Shared C consumes Solve IR and arithmetic, with explicit adapter-owned
constant/type bindings for object and call execution. The eFMI backend consumes
the DAE-derived checked GALEC product for Algorithm Code; Production Code must
consume its Solve algorithm refinement. Neither backend performs that lowering.
Parser, core and all backends never import the compiler package. A new backend belongs beside backend-fmi3 and
must supply its own target contract before its output gains a formal guarantee.

Each language frontend owns its EBNF and generated Lean tables together. The
generic engine owns preprocessing and supplies namespace-parameterized generators.
`lake run generate` regenerates both proof and runtime tables; `lake run check-generated`
detects drift. Relocating the grammar does not enlarge the admitted language.

Use these commands from the repository root inside `nix develop`:

| Command | Purpose |
| --- | --- |
| `lake build` | Build the compiler and runner default libraries and executables |
| `lake build rumoca_compiler` | Build that package explicitly |
| `lake -d packages/compiler build` | Build it as its own workspace |
| `lake build check-packages` | Build all library modules, including separate proof modules |
| `lake build check-sha1` | Check the independent SHA-1 library and its proof/audit library |
| `lake build check-xml` | Check the independent XML library and its proof/audit library |
| `lake build check-parser check-modelica-parser check-galec-parser check-core check-c check-fmi3 check-efmi check-compiler` | Check selected packages and their cached proof/audit libraries |
| `lake build check-lsp rumoca-lsp` | Check and build the independent Modelica language server |
| `lake run frontend-test` | Exercise native LSP and bounded multi-file parsing |
| `lake build audit` | Build all cached package checks, enforcing the axiom whitelist in Lean |
| `lake test` | Required full Lean, artifact, rejection and native C gate |
| `lake run lalr-test` | Development LALR generation and native/actual-table checks; full proof audit is in `lake test` |
| `lake run demo` | Compile and run the example |
| `lake run fmu` | Create and validate `build/Integrator.fmu` with ME and CS |
| `lake run fmi-test` | Build the FMI packages and run archive/importer/ABI checks |
| `lake run efmi-algorithm-test` | Check second-grammar reuse and actual Algorithm Code artifacts; no eFMU claim |
| `lake run efmi-production-test` | Check eFMU publication, actual archive/source binding, native methods and artifact mutations |
| `lake exe rumoca examples/Integrator.mo` | Emit C to stdout from the shared workspace |
| `lake exe rumoca parse --jobs 4 --json examples/Integrator.mo` | Parse independent files with deterministic output and structured byte ranges |
| `lake exe rumoca verify-algorithm build/Integrator.alg --source examples/Integrator.mo` | Check an actual GALEC member and both source grammars |
| `lake exe rumoca examples/Integrator.mo -o build/Integrator.efmu` | Stage, kernel-check and publish the tiny Algorithm/Production Code archive |
| `lake exe rumoca verify-efmi build/Integrator.efmu --source examples/Integrator.mo` | Check the complete actual archive against the source and both grammars; a prepared directory is also accepted |
| `bash scripts/verify-artifact.sh examples/Integrator.mo build/checked` | Check actual source and C files |
| `nvim --headless '+luafile nix/check-editor.lua'` | Check Lean highlighting and the live LSP |

The root `lakefile.lean` coordinates package builds and integration commands.
Its default target delegates to the compiler and runner packages; its test
driver runs the complete gate. Package check targets use Lake's native build
graph, while scripts run the existing cross-package checks in `tests/` and
`scripts/`. It contains no language implementation or semantic proof.
Package artifacts live in each package's `.lake/build`; dependencies are
shared through the active workspace's `.lake/packages`. `build/` contains local
generated examples, certificates and test logs. Both build directories are
ignored by Git.

Use the [incremental development workflow](development.md) for package-local
iteration. Keep one root workspace to reuse dependency caches. A package's
`lake test` builds its check library; cross-package artifact checks stay in the
root `lake test` gate.
