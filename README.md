# Lean Rumoca

A fresh implementation of a **tiny Modelica 3.7 compiler in Lean**. The grammar
tooling, compiler, source and target semantics, and every proof are Lean.
Rumoca's AST → Flat → DAE → Solve separation and CompCert's pass-by-pass proof
approach are design references; neither is a dependency.

The numerical compiler core has checked semantic-preservation proofs. The
complete FMI/eFMI compiler does **not yet have full verification coverage**:
adapter execution and complete artifact/compliance obligations remain open.
No further grammar expansion is allowed until the current admitted subset has
that complete end-to-end guarantee; passing individual proofs or CI is not
sufficient. See the [verification contract](docs/verification.md) and
[remaining obligations](dev/roadmap.md).

This repository is an experimental home for Rumoca's formally verified core.
The plan is to merge it back into [Rumoca](https://github.com/CogniPilot/rumoca)
once the core has been vetted and WebAssembly (WASM) deployment has been tested.
Those milestones remain prerequisites for reintegration.

The production compiler currently admits this Modelica profile:

```modelica
model Integrator
  Real x;
equation
  der(x) = 1;
end Integrator;
```

Model and state names can vary. ASCII identifiers and spaces/tabs/CR/LF are
accepted; declaration/reference and model/end names must agree. This profile
has one state, one equation and only the literal `1`. Comments, modifiers,
initial equations and general expressions are rejected.

This source leaves the initial state free. The default FMU/eFMU plan selects
zero and reports both the Real fallback and the selected initial condition at
the declaration. Scalar Flat/DAE/Solve models carry mandatory checked provenance
for those decisions. See [initialization coverage](dev/initialization.md) for
the proofs and remaining adapter obligations.

The production compiler also admits the pointwise tensor array profile shown in
`examples/TensorSquare.mo`:

```modelica
model TensorSquare
  input Real u[2];
  output Real x[2](each start=0, each fixed=true);
  output Real J[2,2];
equation
  der(x) = u .* u;
  J = jacobian (u .* u, u);
end TensorSquare;
```

It carries a two-element input, a fixed-start output state, the elementwise
product `.*` and a square `jacobian` output (`jacobian` is an identified
language extension). This profile is admitted for FMI 3 FMU output, whose
publication gate is the fixed `tensor-fmi3` source-build certificate, and for
tensor eFMI Algorithm Code (`.alg`) output, whose publication gate is the fixed
`tensor-algorithm` certificate; the default `rumoca` CLI dispatches the array
profile to `compileTensor` and the corresponding checked publication path.
Tensor complete eFMU (`.efmu`) archive export and tensor C emission are rejected
with a diagnostic, and the scalar driven profile
(`examples/DrivenIntegrator.mo`) stays rejected. Tensor rank and extents remain
symbolic in the shape parameter; no tensor element is enumerated during
lowering. See the [IR alignment review](dev/ir-review.md),
[tensor AD notes](dev/tensor-ad.md) and
[FMI 3 proof obligations](dev/fmi3/contracts.md). Either admitted profile can be
packaged as one FMI 3 FMU containing both Model Exchange and Co-Simulation. The
numerical kernels are formally checked; full FMI adapter execution verification
remains open.

The production compiler also admits the constant-rate profile shown in
`examples/ConstantRates.mo`:

```modelica
model ConstantRates
  Real x;
  Real y;
equation
  der(x) = 2.5;
  der(y) = -1;
end ConstantRates;
```

It carries two or more scalar states, each with one `der(state) = literal`
equation whose right-hand side is a signed decimal literal; the equation order
is immaterial. Each rate is the round-to-nearest-even of its literal's exact
base-ten content. This profile is admitted for FMI 3 FMU output, whose
publication gate is the fixed `constant-fmi3` source-build certificate; the
default `rumoca` CLI dispatches the constant profile to `compileConstant` and
the corresponding checked publication path. Constant eFMI Algorithm Code, eFMU
archive export and C emission are rejected with a diagnostic. The state count
stays symbolic in the model's shape parameter; no rate coordinate is enumerated
during lowering.

## Run

The default `nix develop` shell includes configured Neovim with Lean syntax
colors, LSP semantic highlighting, completion and a goal infoview:

```sh
nix develop
nvim packages/compiler/Rumoca/Lowering.lean
```

See [editor setup and keys](docs/editor.md). Re-enter the shell after changing
the configuration. The `verification` shell below stays minimal for CI.

Lean **4.29.1** and mathlib are pinned. The Nix shell supplies Elan, which
installs the official Lean release selected by `lean-toolchain`, plus a C11
compiler, ZIP tools and FMPy on x86_64 Linux. It does not require Rocq,
Coq or CompCert. For a fresh checkout, fetch mathlib's already-checked proofs
using the [initial setup commands](docs/development.md#initial-mathlib-cache)
before running the verification gate:

```sh
nix develop .#verification
lake test
lake run demo
```

Subsequent builds reuse Lake's native cache. CI fetches missing upstream proofs
and requires them to pass Lake's `--no-build` check, even on its first run.

`lake run demo` compiles the example to C and runs three unit-time steps from 0.5:

```csv
t,x
0,0.5
1,1.5
2,2.5
3,3.5
```

To run another admitted model:

```sh
lake build
mkdir -p build
packages/compiler/.lake/build/bin/rumoca examples/Integrator.mo -o build/model.c
cc -std=c11 -O2 -fno-fast-math -ffp-contract=off \
  build/model.c examples/driver.c -lm -o build/simulate
./build/simulate 3 -1.5
```

The source state is mathematically real; generated C stores it as IEEE754
binary64 `double`. The host supplies the initial value and selects
round-to-nearest, ties-to-even. Finite fractional, negative and subnormal
starting values are supported. The count is separate `uint64_t` control data.
Sampling is still at integer times: there is no variable time step or general
numerical solver. Host decimal conversion and CSV output are tested C code.

To create and run the FMU, use the separate runner package:

```sh
lake run fmu
lake exe fmu-runner validate build/Integrator.fmu
lake exe fmu-runner simulate build/Integrator.fmu --mode cs \
  --variable x --start x 0.5 --stop 3 --step 1 --csv build/Integrator-cs.csv
lake exe fmu-runner simulate build/Integrator.fmu --mode me \
  --variable x --start x 0.5 --stop 3 --step 1 --csv build/Integrator-me.csv
```

Both runs produce `x = 0.5, 1.5, 2.5, 3.5` at times `0, 1, 2, 3`. CS embeds
the existing unit-step solver over the shared model. ME uses the importer's
solver (FMPy Euler in these commands). CS accepts integer multiples of its
internal step of 1, up to one million per call; it discards unsupported steps
without advancing. `x` stays a local variable, as declared by the source.

Compare both FMU interfaces side by side with OpenModelica on the same source:

```sh
nix develop .#comparison --command lake run compare-omc
```

The optional comparison shell adds pinned OMC. Reports, raw CSV traces and logs
stay under `build/omc-comparison/`. See [comparison settings and limits](docs/omc-comparison.md).
Numerical agreement is integration evidence, not a replacement for the proofs.

`rumoca MODEL.mo -o MODEL.fmu` checks the actual numerical C file in Lean,
builds a native Linux binary and validates the archive before publishing it.
The FMU also contains C sources and `buildDescription.xml`. Binary compatibility
is with the build host's architecture and libc; this is not a universal binary.
ME state/derivative access and internal numerical helper calls have body proofs.
The remaining FMI lifecycle, time, lifetime and complete archive binding still
need proofs; see [the roadmap](dev/roadmap.md#fmi-3-architecture-requested-during-this-review).

The same unit profile can produce a checked eFMU containing GALEC Algorithm
Code, Production C, correlated manifests and the pinned eFMI schemas:

```sh
lake exe rumoca examples/Integrator.mo -o build/Integrator.efmu
lake exe rumoca verify-efmi build/Integrator.efmu --source examples/Integrator.mo
```

The publisher kernel-checks the complete staged archive against the source and
both grammars before replacing the destination. `ArchiveContract` connects its
GALEC, C execution, XML mappings and exact ZIP bytes. This covers our authored
tiny profile; complete standards conformance remains under [eFMI review](dev/efmi.md).
The pinned official checker cannot read the selected standalone layout;
[SR06](dev/standards-review.md#sr06--resolved-packaging-question-documented-checker-limitation)
records that tool limitation. No official-checker pass is claimed.

## Verification

For the editing loop, use `lake build check-parser`, `lake build check-core`,
`lake build check-fmi3`, `lake build check-efmi`, or `lake build check-compiler` from the root
workspace. Each builds only its package's library/check targets and changed
dependencies. See [incremental development](docs/development.md).

`lake test` checks the proofs, axiom dependencies, generated grammar freshness,
actual source/C certificates, mutation rejection, native C execution, FMI
schema validation, independent ME/CS importer runs and raw ABI regressions.

| Layer | Lean guarantee |
| --- | --- |
| Modelica lexer/parser | Soundness and completeness for the authored tiny source grammar |
| EBNF generation | Exact embedded reader result and recursive expression-to-CFG language preservation |
| Generic LALR | Grammar membership iff parser success, with checked bounds and rejection for every input |
| AST → Flat → DAE → Solve | Name resolution and equation/derivative preservation |
| Solve → C AST | RHS preservation and exact rounded-step preservation |
| Emitted C | Exact output bytes checked; structural printer proofs establish denotation in the independent admitted C grammar |
| eFMI archive | Actual source, both grammars, GALEC, Production C behavior, correlated XML and every stored-ZIP member bound in one kernel-checked contract |
| Binary64 | Bijection with finite 64-bit encodings; signed zeros; nearest/even rounding; no overflow for any finite `x + 1` |
| C statements | Explicit scope, assignments, modular uint64 decrement, sequencing, loops and returns; all calls terminate with the exact Solve result |
| Whole compiler | Every C behavior is an allowed source numerical-profile behavior, and conversely; stuck execution and divergence excluded |
| Real refinement | Unique real ODE solution; exact representable sample horizons; nearest rounding and half-spacing bounds; global error after `n` steps ≤ `n` |
| FMI lifecycle guards | The generated guard AST implements the authored reference rules for the selected commands; this does not cover the whole adapter |
| ME state-access bodies | Actual generated get/set trees preserve exact binary64 state and frame other memory under explicit storage preconditions; printed adapter binding remains open |
| FMI helper calls and ME derivative body | Explicit call frames execute the numerical C statements; internal advancement agrees with shared CS model state and the derivative getter writes the shared ME derivative; public CS time/lifecycle and ABI binding remain open |
| ME time update | Binary64 comparison results refine real order; the generated guard accepts the represented history window and successful time updates preserve model state; history maintenance and rejected-call paths remain open |

The global bound includes stagnation: at `x = 2^53`, adding `1` rounds back to
`x`. It is a conservative bound, not a precision claim. The rounding definition
is a mathematical specification over finite encodings; it is never enumerated
by the executable compiler. Native C uses hardware double arithmetic.

`Rumoca.compiler_semantic_preservation` is the high-level behavior theorem.
`Rumoca.compile_verified` supplies the artifact contract from which it follows,
including actual source/output binding, source parsing, certified C printing, scoped execution and real
refinement.
Each IR edge has a named `lower_correct` theorem; see
[the pass contract table](docs/verification.md#parser-and-pass-contracts).
The behavioral theorem now composes the real pass relations through an explicit
unit-step numerical policy. `compiler_preserves_property` transfers properties
of source observations to every behavior of the actual emitted C output.
Check a particular file with:

```sh
bash scripts/verify-artifact.sh examples/Integrator.mo build/checked-model
```

The checker independently reads the actual files and constructs the theorem
it must prove. A producer-supplied certificate or a proof about different C
bytes cannot authorize the artifact. Both review attacks are regression tests.

There are no proof placeholders, added axioms or native-reduction proof axioms.
The audit permits only Lean's `propext`, `Classical.choice` and `Quot.sound`.

**Proof boundary:** target execution means the authored small C semantics in
Lean under the binary64/nearest-even ABI profile. Alignment with ISO C, IEEE754
and the Modelica prose standard remains a specification review obligation.
GCC, hardware execution, linking, file I/O and the CSV host are outside the
proof. This is not CompCert's verified C-to-assembly pipeline. Read
[the exact contract](docs/verification.md) before extending the core.

Before each grammar expansion, complete the
[recurring standards review](dev/standards-review.md#required-review-at-every-spiral-stage)
for the entire admitted subset: Modelica Language Specification (MLS), FMI 3
ME/CS, and eFMI GALEC/Production Code. Record clause-to-proof correspondence,
actual-artifact evidence and remaining assumptions. Open compliance findings
or missing compiler proofs block expansion, even when CI passes.

## Packages and grammar generation

The repository is a workspace containing nine Lake packages:

| Package | Responsibility |
| --- | --- |
| [verification](packages/verification/README.md) / `ProofAudit.*` | Shared Lean axiom audit command used by cached package checks |
| [sha1](packages/sha1/README.md) / `SHA1.*` | Independent SHA-1 implementation, proofs and checksum certificates |
| [xml](packages/xml/README.md) / `XML.*` | Independent XML renderer, restricted syntax and correctness proofs |
| [parser](packages/parser/README.md) / `Parser.*` | Generic EBNF tools, LALR runtime and typed actions, scanner, source spans and proofs |
| [modelica-parser](packages/modelica-parser/README.md) / `ModelicaParser.*` | Modelica EBNF, generated LALR tables, AST actions and instance proofs |
| [galec-parser](packages/galec-parser/README.md) / `GALECParser.*` | GALEC EBNF, generated LALR tables, syntax actions and instance proofs |
| [core](packages/core/README.md) / `RumocaCore.*` | Shared Flat/DAE/Solve IR, finite arithmetic and transition semantics |
| [backend-c](packages/backend-c/README.md) / `RumocaC.*` | Shared Solve → C emission, certified printers and execution proofs |
| [backend-fmi3](packages/backend-fmi3/README.md) / `RumocaFMI3.*` | FMI interfaces, lifecycle proofs, XML and FMU packaging |
| [backend-efmi](packages/backend-efmi/README.md) / `RumocaEFMI.*` | Tiny checked GALEC and Production C; complete eFMU artifact verification remains open |
| [compiler](packages/compiler/README.md) / `Rumoca.*` | CLI, source semantics, pass composition, whole-compiler theorem and artifact checker |
| [fmu-runner](packages/fmu-runner/README.md) / `FMURunner` | Independent Lean CLI reusing FMPy for FMU inspection, validation and ME/CS simulation |

The compiler depends on parser, core and both backends, with parser → core → backend
as the underlying dependency order. The root `lakefile.lean` delegates plain
`lake build` to the compiler and runner packages' default targets.
The backend takes Solve IR as input; another generator can use that boundary
without taking ownership of the frontend. Runtime APIs and mathematical proof
modules have separate imports. See each package's README for independent builds.

Repository-wide checks live in `tests/`; package-specific Lean checks live in
each package's `Tests/` directory. `scripts/` contains reusable verification
commands, `examples/` holds the Modelica example and its C host, and `nix/`
contains the development editor and its integration check. See the
[repository layout guide](docs/layout.md) for ownership and common commands.

[packages/modelica-parser/grammar/Modelica.ebnf](packages/modelica-parser/grammar/Modelica.ebnf) is compiled by `lake run generate`.
The Lean generator accepts terminals, `IDENT`, comma or implicit sequences,
`|`, `(...)`, `[...]`, `{...}`, empty terminals and recursive named rules.
Modelica and GALEC use one in-tree LALR engine. Independent EBNF semantics,
checked lowering witnesses and table certificates establish acceptance
preservation, completeness and an input-size execution bound. The old DFA
path has been removed.

The reusable typed-action interface gives frontends the concrete syntax tree
and original tokens while allowing user-defined ASTs. Existing profiles prove
membership by EBNF derivation; changing the grammar alone does not extend the
compiler's semantic language. Source lexing, spans and lowering contracts remain
separate obligations composed by the compiler. See the
[LALR proof plan](dev/lalr-parser.md) for remaining diagnostic and
generator cost/convergence work. Generated located parsing now has exact
result agreement with ordinary parsing and uses the same certified bound.
The span increment passed the full local proof and actual-artifact gate.
The EBNF text reader now has checked soundness and completeness against
independent character and token syntax, using its normal input-size budgets.
That reader increment passed the full proof and actual-artifact gate for both targets.

Reused foundations are Lean's standard library and mathlib's CFG languages,
finite sets, integer arithmetic and real analysis. See
[design and references](docs/design.md) for the package survey and Rumoca specs.

Track assurance gaps, pass contracts, release gates and verified language
expansion in the [compiler roadmap](dev/roadmap.md). Completed baseline proofs
are distinguished from the open work required for broader assurance claims.

GitHub Actions runs the package audits and full verification gate on pushes and
pull requests. See [CI and incremental development](docs/development.md#github-ci)
for commands, caching and retained evidence.
