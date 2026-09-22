# Trust and premise ledger (K05)

**Runtime tensor finiteness scanner (2026-09-22; full gate passed):**
The emitted scanner now executes the core all-finite classifier in the authored
C semantics, including typed parameter/return conversion and canonical contextual
calls. Its complete heap is unchanged. Nonempty input requires all indexed
cells readable; empty input may be null. Count bounds, explicit header types
and exact function lookup are retained. The fixed development actual-file
certificate binds bytes, independent syntax, exact returned flag and execution;
it does not assert that public FMI/eFMI methods call this helper. Owning builds,
bounded independent review, actual-file certification, mutation rejection and
the existing native driver passed. The required full gate passed with all
2,450 inputs unchanged, all 7,640 printed axiom reports (wrapped lists included),
all 16 new roots and four retained FMU roots passing the unchanged whitelist.
All three FMI matrices and scalar/tensor eFMI actual-byte, publication/reuse,
mutation and native checks passed. Only three evidence documents changed after
the frozen gate. Native
headers/`isfinite`, exception configuration and machine correspondence remain
outside the Lean model. No axiom or audit policy changed. N01, all-path detection
and interface failure protocols, source histories, MISRA and K02–K05 remain
open. See `build/tensor-finite-scan-checkpoint.md`.

**Numerical classification foundation (2026-09-22; full gate passed):**
The core detector is proved against all finite/nonfinite encoding classes, and
its tensor lift covers all coordinates. The square detector accepts exactly
the existing finite-execution domain and otherwise witnesses real overflow.
The actual multiplication-helper contract retains its execution/storage/frame
fields and additionally classifies the same final heap using the authored C
value check. No emitted runtime scanner or interface failure handling is added;
native classifier correspondence and the N01/MISRA detection obligation remain
open. Owning modules, bounded independent review and the affected-package
rebuild passed (4,289 jobs, all 20 new roots and 5,402 permitted printed axiom
reports, wrapped lists included). The required full artifact gate passed with
all 2,444 inputs unchanged, all 20 new roots, all 7,608 permitted printed axiom
reports and four permitted retained FMU roots. All three FMI matrices and the
scalar/tensor eFMI actual-byte/reuse/mutation/native checks passed. Only the
three evidence documents were updated after the gate. See
`build/numerical-detection-checkpoint.md`. N01 and K02–K05 remain open.

**Finite-input multiplication outcomes (2026-09-22; full gate passed):**
The authored C multiplication rule now returns the independently specified
finite/infinite result for finite operands. `mulResult_finite_iff` proves exact
conservativity of the finite operation, including zero encodings. The new tensor
helper proof reuses typed array storage; finite heap specialization and the
outside frame are retained. Mandatory `multiplicationOutcomes` fields bind the
new helper contract to actual text in both artifact paths. Legacy fields remain.
Focused independent review and native helper rehearsals passed. The complete
affected package rebuild passed 4,286 jobs, all 32 new roots and all 5,382
printed axiom reports under the unchanged whitelist. The required full artifact
gate then passed with all 2,440 inputs unchanged, all 32 new roots, 7,583
permitted printed axiom reports and four permitted retained FMU roots. All three
FMI matrices and scalar/tensor eFMI actual-byte/reuse/mutation/native checks
passed. See `build/multiplication-outcomes-checkpoint.md`.
Nonfinite operands, source trajectories/public-method overflow, exceptions/traps,
size bounds and native correspondence remain outside this increment. F3/K05
are not closed.

**Encoded Jacobian helper outcomes (2026-09-22; full gate passed):**
`SquareDiagonal.Total.storage_correct` removes the finite-output premise for
the unchanged helper on arbitrary finite inputs. The result is the independently
specified nearest-even finite/infinite encoding, with exact finite-heap
specialization, matrix reads and outside frame. Mandatory `jacobianOutcomes`
fields bind this result to actual numerical text in both FMI and eFMI products.
Legacy fields remain. Package checks (3,675 jobs, 24 new roots) and a native
rehearsal and focused independent review passed. The required full artifact
gate then passed with all 2,429 inputs unchanged, all 24 new roots, 7,530
permitted printed axiom reports (wrapped lists included), and four permitted
retained FMU roots. All three FMI matrices and eFMI actual-byte/reuse/mutation/
native checks passed. See `build/jacobian-overflow-checkpoint.md`.
F3 is only narrowed: source RHS/public-method overflow, nonfinite
inputs, size bounds, exceptions/traps and native correspondence remain open.
No K05 closure follows.

**Finite-square derivative premise (2026-09-22; full gate passed):** The new
mandatory `TensorExecutedProductionContract.finiteSourceDoStep` derives the
Jacobian coefficients and their finite additions from finite square RHS
execution. `Binary64.ADExact.finite_square_doubling` proves the domain implication
universally, and `ArrayProfile.ADExact.coefficient_adds_from_finite_rhs` retains
exact encodings. This premise is proved, not external. The old `sourceDoStep`
field remains unchanged. Source/actual-byte/final-heap bindings and storage
premises remain; primal overflow and other numerical/history/native obligations
are not discharged. Package checks and focused independent review passed. The
required full artifact gate passed with unchanged inputs, all seven new roots,
7,378 permitted printed axiom reports and four permitted retained FMU roots.
All three FMI matrices and eFMI actual-byte/reuse/mutation/native boundary checks
passed; see `build/finite-square-checkpoint.md`. No K05 closure or grammar
expansion follows.

**Canonical-context integration, full gate passed (2026-09-22):** The tensor eFMI actual-file
products now retain the old contracts and additionally require the public-method
execution/source-Jacobian products on the same source, bytes and final heap.
The common C evaluator/scheduler threads declared record/array metadata, with
empty-context legacy wrappers. Allocated storage, finite RHS/addition, external
calls and other stated premises are retained; no arbitrary-outcome, complete
history or native-correspondence claim follows. The integrated required artifact
gate passed with unchanged inputs: all 462 new package roots were present and
all 7,477 printed axiom reports plus four retained FMU roots were permitted.
All three FMI matrices and scalar/tensor eFMI artifact/reuse/mutation checks passed.
The extended native boundary executes extracted tensor public methods, including
finite and signed-zero cases; it does not prove host compilation or ABI. See
docs/verification.md and the canonical consumer checkpoint for evidence.
No K05 item is closed by this integration.

This ledger records, for every mandatory actual-artifact contract in the frozen
subset, the theorem quantifiers, the classification of each premise, the
all-behavior coverage of the emitted interfaces, the non-vacuity evidence, and
the axiom-audit trust roots. It is the premise and trust ledger required by
roadmap package K05. It ticks nothing: it is a review record, not a closure
claim.

**Numerical applicability repair (2026-09-21, full gate passed):** The prior FMI type
dictionary omitted the shared numerical helpers' `double *` and `const double *`
parameter spellings. The Lean diagnostics `NumericalHeaderGap.fenv_header_missing`
and `fenv_library_missing` prove, universally over literal tables, fenv headers
and definition tables, that that standard tensor fenv interface could not satisfy
the binary header/full-library premise. Both roots passed the whitelist in
`build/kernel-header-gap-diagnostic.log`. Thus the conditional accepted-step
products are not evidence of executable tensor linkage in that interface.
The reviewed actual numerical table also omits unused sub/div definitions, so
repair requires both real header bindings and instruction-restricted library
contracts, followed by mandatory same-source tree-table execution composition.
The combined repair is now promoted: actual pointer bindings, restricted
canonical proofs, exact numerical trees, and mandatory compiled-IVP/actual-byte/
prepared-rejection/accepted-runtime composition. The accepted product derives
its internal header/library/lookup/resolution facts; original memory, finite
arithmetic and external math assumptions remain. Its concrete dictionary and
source instantiation passed the coherent package rebuild (4,163 jobs; all 150 new
roots and 4,857 printed axiom lists permitted). A proof-elaboration repair made
the event-type binder explicit without changing any statement. The required full
artifact gate passed (exit 0, observed 22:12 UTC) with unchanged implementation
inputs, all 150 new roots, and all 6,753 printed axiom lists permitted. The four
retained FMU source/C/build roots also use only permitted axioms. All three FMI
matrices and the scalar/tensor eFMI publication/reuse/mutation controls passed.
This validates the repair, not full coverage or native correspondence. In
particular, tensor eFMI's native boundary here compiles its C but does not execute
its complete public methods. Existing warnings remain. Evidence is
tracked in `build/numerical-linkage-checkpoint.md` and
`/tmp/rumoca-numerical-promotion.KRyn7b/README.md`. The earlier step-composition
gate and this new numerical-linkage gate are separate validation checkpoints.

Premise classes used throughout:

- **proved**: discharged by a Lean theorem over the universally quantified
  model; the discharging theorem is named.
- **checked**: decided by a fixed artifact checker on the *actual* bytes of the
  emitted file (a `verify_*` elaborator or `#audit`), reducing by `decide`,
  `rfl`, `Eq.refl`, or a certificate that reads the real file; the check is
  named. Candidate bytes are never proof authority: the checker only rejects.
- **external**: assumed of the platform, importer, toolchain, headers, or
  library/runtime, outside the Lean model. The exact assumption is stated.

The trusted foundational axiom set for every gate is
`{propext, Classical.choice, Quot.sound}` (see section 5); every checker rejects
any other axiom in the closure of the contract it certifies.

Contracts and file:line (Lean names):

| Contract | Definition | Discharge theorem | Fixed checker (elaborator) |
|---|---|---|---|
| `Rumoca.ArtifactContract` (scalar C) | `Verified.lean:42` | `Rumoca.artifact_correct` `Verified.lean:75` | `ArtifactCheck.check` / `verify_artifact` (`Tools/CheckArtifact.lean`) |
| `FMI3.SourceBuildContract` (scalar) | `FMI3BuildProofs.lean:14` | `FMI3.sourceBuild_correct` `FMI3BuildProofs.lean:22` | `verify_fmi3_build_files` (`Tools/CheckFMI3Build.lean`) |
| `FMI3.AdapterContract` | `FMI3AdapterProofs.lean:61` | `FMI3.adapter_correct` `FMI3AdapterProofs.lean:121` | via `FMI3AdapterCertificate.certify` |
| `Rumoca.TensorSourceBuildContract` | `TensorProduction.lean:293` | `Rumoca.tensorSourceBuild_correct` `TensorProduction.lean:332` | `verify_tensor_fmi3_build_files` (`Tools/CheckTensorFMI3Build.lean`) |
| `FMI3.TensorAdapter.Contract` | `TensorAdapterContract.lean:52` | `FMI3.TensorAdapter.render_contract` `TensorAdapterContract.lean:160` | via `TensorFMI3AdapterCertificate.certify` |
| `IVPEntry.ArtifactContract` (tensor C) | `RumocaC/TensorSquareIVPEntry.lean:270` | `IVPEntry.artifact_correct` `:274` | `verify_tensor_ivp` (`Tests/TensorCChecks/ArtifactCheck.lean`) |
| `EFMI.AlgorithmContract` | `EFMIProofs.lean:13` | `EFMI.algorithm_correct` `:38` | `verify_efmi_algorithm_files` |
| `EFMI.ProductionContract` | `EFMIProductionProofs.lean:16` | `EFMI.production_correct` `:60` | `verify_efmi_production_files` |
| `EFMI.ManifestContract` | `EFMIManifestProofs.lean:13` | `EFMI.manifests_correct` `:52` | `verify_efmi_manifest_files` |
| `EFMI.ArchiveContract` | `EFMIArchiveProofs.lean:11` | `EFMI.efmu_archive_correct` `:46` | `verify_efmi_archive` |

All file paths are relative to `packages/compiler/Rumoca/` for the compiler
contracts, `packages/backend-fmi3/RumocaFMI3/` for the adapter contracts,
`packages/backend-c/` for the C kernel contracts, and `packages/compiler/Tools/`
for the fixed checkers, unless a fuller path is given.

---

## 1. Scalar FMI 3 source-build contract

`FMI3.SourceBuildContract a c description adapter metadata`
(`FMI3BuildProofs.lean:14`) is discharged by `FMI3.sourceBuild_correct`
(`:22`) and bound to the actual staged files by the fixed elaborator
`verify_fmi3_build_files` (`FMI3BuildArtifactCheck.lean:25`), which reads
`extra/.../Source.mo`, `sources/model.c`, `sources/fmi3.c`,
`sources/buildDescription.xml`, `modelDescription.xml`, the pinned
`Modelica.ebnf`, and the pinned `vendor/fmi3/fmi3FunctionTypes.h`, then emits the
theorem `Rumoca.CheckedFMI3Files.source_to_build` and audits its axiom closure
(`:112-116`).

The structure has six conjuncts.

### 1.1 `numerical : Rumoca.ArtifactContract a c .internal` (`:15`)

Passed through unchanged from `Rumoca.CheckedFiles.source_to_c`, whose
`ArtifactContract` is produced by `Rumoca.artifact_correct` (`Verified.lean:75`).
Its own fields (`Verified.lean:44-73`) classify as:

| Field (`Verified.lean`) | Discharge / check | Class |
|---|---|---|
| `bytes : a.cSource .internal = c` (`:44`) | `ArtifactCheck.check` reduces the actual `model.c` bytes by kernel `decide` | **checked** |
| `source_lexes` (`:45`) | `parsed_lexes a.parsed` | proved |
| `source_ebnf` (`:46`) | `parsed_in_ebnf a.parsed`; the grammar identity `Generated.source = <ebnf>` is decided on the actual `Modelica.ebnf` bytes | proved (+ **checked** grammar identity) |
| `c_grammar` (`:47`) | `CSyntax.module_render` | proved |
| `rhs_preserved` (`:48`) | `compiler_correct a.solve` | proved |
| `execution` (`:50`) | `execution_correct a.solve` (`Verified.lean:28`) | proved |
| `well_scoped` (`:51`) | `CStatements.lower_scoped` | proved |
| `statements` (`:52`) | `CStatements.denotes_statements` | proved |
| `behaviors` (`:54`) | `CStatements.lower_behavior_correct` | proved |
| `call_termination` (`:57`) | `CStatements.all_terminate` | proved |
| `call_completion` (`:59`) | `CStatements.all_complete` | proved |
| `real_solution_refinement` (`:63`) | `CStatements.real_refinement` | proved |
| `model_exchange` (`:68`) | `CStatements.model_exchange_correct` | proved |
| `co_simulation` (`:71`) | `CStatements.co_simulation_correct` | proved |

`ExecutionContract` (`Verified.lean:14`), carried by `execution`, adds the
finite-arithmetic outcome premises: `rounding_error` (`:23`) and
`counter_safe` (`:25`) are proved over the authored `Binary64` IEEE model.

**External boundary of 1.1.** The `.c` grammar and the `Binary64` IEEE
interpretation are *authored Lean specifications*; that a real C toolchain and
host ABI realise those semantics after machine compilation is **external**
(`Verified.lean:7-10`). The finite-arithmetic outcomes are proved *inside* the
authored model; the identity between that model and the executing hardware is
the trusted boundary.

### 1.2 `build : Build.ArtifactContract a.parsed.ast.name description` (`:16`)

Discharged by `text ▸ Build.artifact_correct _ (parsed_name a.parsed)` in
`sourceBuild_correct`. The recipe-correctness theorem `Build.artifact_correct`
is **proved**; the hypothesis `text : XML.document (Build.description name) =
description` is **checked** on the actual `buildDescription.xml` bytes by the
rejection `description != XML.document buildTree` (`FMI3BuildArtifactCheck.lean:42`)
and the certificate `XML.CertificateCheck.certify` (`:51`). The model-name law
`parsed_name` is **proved**.

### 1.3 `source_prefix : SourcePrefixContract a.parsed.ast.name adapter` (`:17`)

Discharged by `FMI3.sourcePrefix_of_chars _ _ (parsed_functionPrefix a.parsed)`
plus `source_prefix_bytes`. The naming law `parsed_functionPrefix` is
**proved**; the prefix
`"#define FMI3_FUNCTION_PREFIX <id>_\n#include \"model.c\"\n" <+: chars`
is `decide +kernel` on the actual `fmi3.c` bytes (`:83-85`), guarded by
`adapter.startsWith expectedPrefix` (`:46`). **checked**.

### 1.4 `model_identifiers : ModelIdentifiersContract a.parsed.ast.name metadata` (`:18`)

Discharged as `⟨mdTree, XML.document_correct mdTree …, identifiers⟩`. The
document-rendering theorem `XML.document_correct` is **proved**; the decode
`FMI3.decodeModelIdentifiers mdTree = some (name, modelIdentifier, modelIdentifier)`
is `decide +kernel` (`:62-64`): **checked**; the identity of `mdTree` with the
actual `modelDescription.xml` bytes is **checked** via `metadata_bytes`
(`:57-58`).

### 1.5 `adapter : AdapterContract a adapter` (`:19`)

`AdapterContract` (`FMI3AdapterProofs.lean:61`) is an existential over the FMI
signature list with 32 conjuncts. It is discharged by the adapter certificate
`FMI3AdapterCertificate.certify` (`FMI3BuildArtifactCheck.lean:74`), which runs
`adapter_correct` (`FMI3AdapterProofs.lean:121`).

- **checked**: the byte identity `Runtime.render a.solve.prepareFMI3 sigs =
  adapter` (`:66`) is established by `adapter_chars` (`:47`), which binds the
  independently read `fmi3.c` bytes to the concatenation of the per-function
  renders; the signature list `sigs` itself is **checked** to be the actual
  `fmi3FunctionTypes.h` signatures via `FMI3.Header.signatures header`
  (`FMI3BuildArtifactCheck.lean:73`); `CTree.Preprocessing.Stable adapter.toList`
  (`:64`) is proved over those checked bytes.
- **proved**: the remaining 30 conjuncts: `Nodup` of names (`:62`),
  `Reset.signature ∈ sigs` (`:65`), `AdapterPrinter.FunctionsContract` (`:68`),
  per-function readiness `CCalls.Signature.Ready` (`:69`), and every per-function
  render contract (`Reset`, `CountQueries`, `Version`, `Logging`, `Nominals`,
  `StateCalls`, `Derivative`, `Float64`, `Float64Set`, `Initialization`,
  `Identity`, `FactoryAdmission`, `StaticRuntime`, `Termination`, `Time`,
  `EventEntry`, `Completed`, `Discrete`, `Step`, `DebugLogging`,
  `EventIndicator`, `DiscreteEvaluation`, `AbsentVariables.FamilyContract`,
  `CapabilityRejection.AllContract`), each from its `*.rendered_contract`
  theorem, and `PublicAPI.Covered sigs` (`:119`) from the kernel-checked
  `fmi_public_coverage` tactic.
- **external**: native ABI and call convention, whole-C preprocessing/macro
  expansion, included-header (`model.c`, `<stddef.h>`, `fmi3*.h`) interpretation,
  and the implementation of native library routines are explicitly retained as
  separate boundaries (`FMI3AdapterProofs.lean:32-35, 187-190, 244-245,
  288-296`). The runtime behavioral consequences (section 3) are additionally
  stated over external bindings `program.externals "floor"`,
  `"fegetround"`, `"atomic_exchange"`, `"atomic_store"` and the host logger
  callback (`FMI3AtomicCalls.lean:33-35`, `FMI3CSLifecycle.lean:27-30`); these
  are assumed to be the modeled `CMathCalls.floorExternal`,
  `CMathCalls.roundingExternal`, `CAtomicBoolean.Calls.*External` and the
  importer-supplied logger.

### 1.6 `metadata : XML.Document (modelDescription a.solve.prepareFMI3) metadata` (`:20`)

Discharged by `XML.document_correct mdTree mdValid` after substituting the
checked artifact identity `a = artifact` (`FMI3BuildArtifactCheck.lean:108`).
The XML validity is `certifyValidity` (`:59`, `decide`): **checked**; the
actual `modelDescription.xml` bytes are **checked** (`:44`, `:57-58`); the
document law is **proved**.

**Scalar FMI source-build totals.** 6 conjuncts; expanding 1.1 and 1.5, the
contract rests on 14 numerical fields + 32 adapter conjuncts + 4 top-level
recipe/prefix/identifier/metadata conjuncts. Premises by class: 1 checked byte
identity per emitted file (5 files: model.c, fmi3.c, buildDescription.xml,
modelDescription.xml prefix/decode/validity), the grammar identity checked, and
the full behavioral content proved; the machine-compilation/ABI/header/library
boundary external.

---

## 2. Tensor build, scalar C artifact, and eFMI contracts

### 2.1 Tensor FMI 3 source-build contract

`Rumoca.TensorSourceBuildContract a modelC buildDescription adapter metadata`
(`TensorProduction.lean:211`) is discharged by `tensorSourceBuild_correct`
(`:237`) and bound to actual bytes by `verify_tensor_fmi3_build_files`
(`TensorFMI3BuildArtifactCheck.lean:39`), whose root theorem
`Rumoca.CheckedTensorFMI3Files.source_to_build` is axiom-audited (`:219-222`).
Seven conjuncts:

| Conjunct (`TensorProduction.lean`) | Discharge / check | Class |
|---|---|---|
| `kernel : modelC = TensorKernel.modelC` (`:213`) | `TensorKernel.chars` (`:196`) binds the concatenated certified fragment renders to the actual `model.c`; each of the nine fragments is `checkPieceEquality`/tree-certified by `Eq.refl` under kernel (`:119-157`), and rejection `!modelC.startsWith`/text compare (`:64`) | **checked** (per-fragment, on the real file) |
| `kernelContract : IVPEntry.ArtifactContract sources jacobianDiagSource` (`:218`) | `IVPEntry.artifact_correct` (see 2.3) | **proved** |
| `build : FMI3.Build.ArtifactContract a.name buildDescription` (`:221`) | `Build.artifact_correct`; actual `buildDescription.xml` bytes checked | proved (+ **checked** bytes) |
| `adapter : ∃ src w, src.name = a.name ∧ ∀[StaticLiterals], TensorAdapter.Contract w a.tensorModel adapter` (`:224`) | `TensorAdapter.render_contract` (`TensorAdapterContract.lean:160`); byte identity `render … = text` checked by the tensor adapter certificate | proved (+ **checked** byte identity) |
| `model_identifiers` (`:227`) | `TensorMetadata.modelIdentifiers_decode` | **proved** |
| `token` (`:230`) | `TensorMetadata.token_attribute` | **proved** |
| `metadata : XML.Document (TensorMetadata.modelDescription …) metadata` (`:233`) | `XML.document_correct`; actual `modelDescription.xml` bytes + validity checked | proved (+ **checked** bytes) |

`TensorAdapter.Contract` (`TensorAdapterContract.lean:52`) is itself a ~40-conjunct
existential over the tensor function list: coverage `PublicAPI.Covered`, the two
family contracts (`TensorAbsentVariables`, `TensorCapabilityRejection`), every
proved tensor behavioral function contract in header order, the storage-block
layout, the identifier/token agreements, and the call-resolution witnesses for
`rumoca_rhs` and `rumoca_square_jacobian_diag`. All are **proved** by
`render_contract` from the per-function `*.contract` lemmas.

**External / not-covered inside 2.1.** `TensorAdapter.Contract` inherits, as
proved-but-open, the two `fmi3DoStep` behaviors that remain open inside
`TensorDoStep.contract`: the off-grid `fmi3Discard` composition and the
header-aware floating-environment interface (`TensorAdapterContract.lean:36-39`).
The seven runtime-interface behavioral functions carry their own
floating-environment header, objects and literal addresses as universally
quantified premises (external instantiation), and the factory/release contracts
are stated over an arbitrary event program `prog` and tag (`:94-97`): the
importer's atomic runtime. The private kernel `model.c` shares the scalar
machine-compilation/ABI/`<stddef.h>` boundary. The tensor path is deliberately
excluded from CLI production admission (`TensorProduction.lean:20-23`).

### 2.2 Scalar C artifact contract

`Rumoca.ArtifactContract a emitted linkage` (`Verified.lean:42`) is the same
contract enumerated in 1.1; discharged by `artifact_correct` (`:75`) and bound
to the actual `model.c`/generated C by `ArtifactCheck.check`
(`ArtifactCheck.lean:14`), the elaborator behind `verify-artifact c` and the
`certify` tool. Its single **checked** premise is `bytes` (the actual emitted C
reduces to the compiled program under kernel `decide`); the grammar identity is
**checked**; the thirteen semantic fields are **proved**; the
machine-compilation/host-ABI/IEEE-realisation boundary is **external**
(`Verified.lean:7-10`). The negative gate `tests/verification-negative.sh`
exercises the checked premise: a mutated `Model.c`, a mutated embedded source,
and a renamed model are each rejected by the kernel, and a mutated cached input
cannot re-authorize bytes.

### 2.3 Tensor C kernel artifact contract

`IVPEntry.ArtifactContract actual actualDiag`
(`Tests/TensorCChecks/IVPEntry.lean:268`) is
`ProgramContract actual ∧ InitialStorageContract ∧ DerivativeStorageContract ∧
actualDiag = jacobianDiagSource ∧ JacobianDiagStorageContract`, discharged by
`IVPEntry.artifact_correct` (`:271`) and bound to actual files by
`verify_tensor_ivp` (`Tests/TensorCChecks/ArtifactCheck.lean`) plus the
per-operation `verify_tensor_helper` checks driven by `tests/tensor-c.sh`.

| Conjunct | Discharge / check | Class |
|---|---|---|
| `ProgramContract actual` | `program_correct actual printed`; `printed : actual = sources` checked on the real IVP files | proved (+ **checked** bytes) |
| `InitialStorageContract` | `initial_call_correct` | **proved** |
| `DerivativeStorageContract` | `derivative_call_correct` | **proved** |
| `actualDiag = jacobianDiagSource` | reflexive check on the real diagonal source | **checked** |
| `JacobianDiagStorageContract` | `jacobianDiag_correct` (bundles `SquareDiagonal.helper_call_correct`, `output_reads`, `output_frame`) | **proved** |

**External.** The storage contracts are stated over an arbitrary
`CLoops.Calls.Definitions` in which the helper names resolve
(`SquareDiagonal.function.signature.name`, `Fill.function.signature.name`),
`CTensor.HeaderTypes`/`Fill.HeaderTypes` hold, and the write region is
`< 2^64` and non-overlapping: the native heap and header realisation are
external. `tests/tensor-c.sh` corrupts a loop bound (`k < count` to `k <=
count`) and a single IVP member and confirms rejection.

### 2.4 eFMI algorithm contract

`EFMI.AlgorithmContract a emitted` (`EFMIProofs.lean:13`) discharged by
`algorithm_correct` (`:38`), bound to the actual `model.alg` by
`verify_efmi_algorithm_files` (`Tools/CheckEFMIAlgorithm.lean`).

| Field (`EFMIProofs.lean`) | Discharge | Class |
|---|---|---|
| `bytes : a.algorithmSource = emitted` (`:16`) | reflexive on the actual `model.alg` bytes | **checked** |
| `source_lexes` (`:17`) | `parsed_lexes` | proved |
| `source_ebnf` (`:18`) | `parsed_in_ebnf`; Modelica/GALEC grammar identities checked on the actual `.ebnf` files | proved (+ **checked**) |
| `grammar_processed` (`:19`) | `EFMI.grammar_processed` (the LALR engine compiles the GALEC grammar to the pinned tables) | proved |
| `parsed` (`:21`) | `render_denotes a.algorithmCode` | proved |
| `dae_admission` (`:22`) | `GALEC.lower_equation_correct` | proved |
| `startup` / `recalibrate` / `step` / `samples` (`:23-26`) | `GALEC.startup_correct`, `recalibrate_correct`, `doStep_correct`, `run_correct` composed with `Solve.Model.*` | proved |
| `solve_refinement` (`:27`) | `GALEC.UnitProfile.lower_correct` | proved |
| `lifecycle_refinement` (`:33`) | `GALEC.Protocol.lower_trace_correct` | proved |

**External.** Production Code member, XML, checksums, ZIP transport, and the
host lifecycle scheduler are explicitly not certified here (`:11-12`).

### 2.5 eFMI production contract

`EFMI.ProductionContract a algorithm c` (`EFMIProductionProofs.lean:16`)
discharged by `production_correct` (`:60`), bound to the actual production C by
`verify_efmi_production_files` (`Tools/CheckEFMIProduction.lean`).

- **checked**: `bytes : a.productionSource = .ok c` (the actual production C
  member reduces to the lowered module render; `production_source_is_unit`
  `:55` fixes the module).
- **proved**: `algorithm_contract` (the AlgorithmContract), `algorithm_names`,
  `header : CHeader.Contract c`, `startup_map : Production.StartupMap.Contract`,
  and the `target` existential: the lowered `Production.Module`, its render, its
  `CSyntax.Denotes`, the typed parameter/return conversions, `Metadata.Contract`,
  the per-method heap-behavior equivalence, the startup-initialization behavior,
  and both directions of the `CProtocol` trace refinement.
- **external**: the physical C compiler, host scheduling, and the archive/XML
  layer (`:9-14`).

### 2.6 eFMI manifest and archive contracts

`EFMI.ManifestContract` (`EFMIManifestProofs.lean:13`) discharged by
`manifests_correct` (`:52`): `identity_valid` (checked against the supplied
identity), `code : ProductionContract`, and a `target` existential establishing
that `Manifest.prepare` yields valid, identified, named documents whose rendered
XML equals the actual algorithm/production/content XML bytes, with the variable
roster and mapped result/status obligations. Rendering laws **proved**; the
actual XML member bytes **checked** by `verify_efmi_manifest_files`.

`EFMI.ArchiveContract a identity bytes` (`EFMIArchiveProofs.lean:11`) is
`∃ code, ManifestContract … ∧ StoredZIP.Format.Conforms (Archive.entries code)
bytes`, discharged by `efmu_archive_correct` (`:46`) via `archive_code_correct`
and `Archive.encode_correct`, bound by `verify_efmi_archive`
(`EFMIArchiveArtifactCheck.lean:14`).

- **checked**: the eFMU member roster (`:21`), each pinned schema resource
  (`:24`, byte compare against the pinned release), and the actual archive bytes
  (`String.fromUTF8?` on the read members, `:27`).
- **proved**: `ManifestContract` and the ZIP `Format.Conforms` transport.
- **external**: the external C compiler, full XSD/prose-standard conformance,
  and the physical archive file I/O and atomic rename (`:9`,
  `EFMIExport.lean:7`).

**Section 2 totals.** Tensor build 7 conjuncts; scalar C 14 fields; tensor C 5
conjuncts; eFMI algorithm 11 fields, production 6 groups, manifest 3 groups,
archive 3 conjuncts. In every contract the emitted-file byte identity is the
checked premise, the semantic content is proved, and the machine
compilation / archive I/O / external-standard layer is external.

---

## 3. All-behavior coverage of the emitted interfaces

Every one of the 75 emitted public functions is a member of exactly one contract
family and is bound into the adapter by `PublicAPI.Covered sigs`
(`PublicAPI.lean:124`), so `PublicAPI.every_export` (`:130`) upgrades the indexed
per-family contract to a statement over every function in the actual signature
list. The `PublicAPI.Entry` enumeration (`:38`) expands to 75: 26 model-facing
entries, 24 absent-typed accessors (12 types x get/set), and 25 unsupported
capability rejections (`CapabilityRejectionFamily.lean:13`, 25 signatures). The
coverage marks below are read from each family's `FunctionContract` fields
(section 1.5) and the corresponding `#audit`-rooted behavioral theorems in
`packages/compiler/Tests/Audit.lean`; every function inherits its family row.

Column key: **P** proved (governing theorem named in the family note); **n/a**
the behavior does not exist for that function; **open** emitted but the behavior
is not yet proved.

### 3.1 Scalar FMI 3 adapter (`FMI3.AdapterContract`), all 75 functions

| # | Family (functions) | Success | Null handle | Lifecycle rej. | Argument rej. | Discard | Suppressed log | Enabled log |
|---|---|---|---|---|---|---|---|---|
| 1 | Version `fmi3GetVersion` | P | n/a | n/a | n/a | n/a | n/a | n/a |
| 1 | DebugLogging `fmi3SetDebugLogging` | P | P | n/a | n/a | n/a | n/a | n/a |
| 4 | Instantiate/free `fmi3InstantiateModelExchange`, `…CoSimulation`, `…ScheduledExecution`, `fmi3FreeInstance` | P | P | P | P | n/a | P | P |
| 2 | Initialization `fmi3EnterInitializationMode`, `fmi3ExitInitializationMode` | P | P | P | n/a | n/a | P | P |
| 1 | Reset `fmi3Reset` | P | P | n/a | n/a | n/a | n/a | n/a |
| 2 | Counts `fmi3GetNumberOfContinuousStates`, `fmi3GetNumberOfEventIndicators` | P | P | P | P | n/a | P | P |
| 1 | Nominals `fmi3GetNominalsOfContinuousStates` | P | P | P | n/a | n/a | P | P |
| 2 | Continuous states `fmi3GetContinuousStates`, `fmi3SetContinuousStates` | P | P | P | P | n/a | P | P |
| 1 | Derivatives `fmi3GetContinuousStateDerivatives` | P | P | P | P | n/a | P | P |
| 2 | Float64 `fmi3GetFloat64`, `fmi3SetFloat64` | P | P | P | P | n/a | P | P |
| 1 | Terminate `fmi3Terminate` | P | P | P | n/a | n/a | P | P |
| 1 | Time `fmi3SetTime` | P | P | P | n/a | n/a | P | P |
| 2 | Mode entry `fmi3EnterEventMode`, `fmi3EnterContinuousTimeMode` | P | P | P | n/a | n/a | P | P |
| 1 | Completed step `fmi3CompletedIntegratorStep` | P | P | P | n/a | n/a | P | P |
| 1 | Discrete update `fmi3UpdateDiscreteStates` | P | P | P | n/a | n/a | P | P |
| 1 | DoStep `fmi3DoStep` | P | P | P | P | P | P | P |
| 1 | Event indicators `fmi3GetEventIndicators` | P | P | P | n/a | n/a | P | P |
| 1 | Discrete evaluation `fmi3EvaluateDiscreteStates` | P | P | P | n/a | n/a | P | P |
| 24 | Absent-typed get/set (float32,int8,uint8,int16,uint16,int32,uint32,int64,uint64,boolean,string,binary) | n/a | P | P | P | n/a | P | P |
| 25 | Capability rejections (Clock, VariableDependencies, FMUState serialize/deserialize, Directional/Adjoint derivative, OutputDerivatives, Configuration/Step mode, ModelPartition, Interval/Shift decimal/fraction) | n/a | P | P | n/a | n/a | P | P |

Governing theorems, by family (`packages/compiler/Tests/Audit.lean` roots and
the `AdapterContract` conjunct `FMI3AdapterProofs.lean:61-119`):

- Version: `FMI3.version_source`; `Version.FunctionContract`.
- DebugLogging: `FMI3.debug_logging_source`; `DebugLogging.FunctionContract`.
- Instantiate/free: `FMI3.adapter_static_create_release`,
  `adapter_static_null_release`, `adapter_quiet_static_creation`,
  `adapter_logged_static_creation`, `prepared_static_rejection`,
  `adapter_quiet_static_rejection`, `adapter_logged_static_rejection`,
  `StaticFactory.Created.source_default`,
  `FactoryValidation.actual_adapter_admission`,
  `scheduled_creation_source` (scheduled execution is a rejecting instantiation).
- Initialization: `FMI3.initialization_source`,
  `InitializationCalls.model_source_initialized`,
  `InitializationCalls.exited_source_initialized`,
  `InitializationCalls.QuietExecutionContract.source`;
  `adapter_static_initialization`.
- Reset: `FMI3.reset_source`, `reset_result`; `Reset.FunctionContract`
  (`successful`, `null`).
- Counts: `FMI3.counts_source`, `counts_failure_source`,
  `counts_runtime_source`; `CountQueries.FunctionContract`
  (`successful`, `null`, `rejected`, `missing`).
- Nominals: `FMI3.nominals_source`, `nominals_runtime_source`.
- Continuous states: `FMI3.state_access_source`; `StateCalls.FunctionsContract`.
- Derivatives: `FMI3.derivative_source`, `derivative_value_source`,
  `runtime_derivative_source`.
- Float64: `FMI3.float64_source`, `float64_set_source`,
  `float64_runtime_source`, `float64_set_runtime_source`,
  `Float64Rejection.Returned.source_recovery`.
- Terminate: `FMI3.adapter_termination`, `Termination.source_frame`,
  `adapter_termination_release`.
- Time: `FMI3.adapter_time`, `TimeCalls.source_frame`, `adapter_time_history`.
- Mode entry / completed / discrete / indicators / evaluation:
  `FMI3.adapter_me_calls`, `adapter_cs_calls`, `event_indicators_source`,
  `event_indicators_me_source`, `discrete_evaluation_source`;
  `EventEntry/Completed/Discrete/EventIndicator/DiscreteEvaluation.FunctionContract`.
- DoStep: `FMI3.adapter_cs_run_history`, `adapter_logged_cs_run_history`;
  `Step.FunctionContract` (`partition`, `cases` = null / accepted / discard /
  reject reason, `logging`): the only function with all seven columns proved.
- Absent-typed: `FMI3.absent_variables_source`;
  `AbsentVariables.FamilyContract` (`SuppressedContract`, `LoggedContract`,
  per-reason rejection).
- Capability rejections: `FMI3.capabilities_source`, `public_functions_source`;
  `CapabilityRejection.AllContract` (`NullContract`, `SuppressedContract`,
  `LoggedContract`): the whole function is the modeled rejection, so the
  "lifecycle rej." column is that unconditional rejection.

**Scalar adapter coverage totals.** 75/75 functions carry a proved per-function
contract and are accounted for by `PublicAPI.Covered`. Success is proved for the
51 model-facing functions and is n/a for the 24 absent-typed and (of the
remaining) not applicable where noted; null-handle behavior is proved for 74
(n/a only for `fmi3GetVersion`, which has no instance argument); suppressed and
enabled logging are proved for every function that logs. No scalar adapter cell
is **open**.

**Native instantiation (scalar).** Every behavior class in this table is now
instantiated natively at least once on the actual `build/Integrator.fmu` by the
all-behavior matrix `tests/fmi3.py --matrix` (run from `tests/fmi3.sh`): 75/75
functions and 514 behavior cells, covering null handle (70 status functions plus
the factory null-handle creation failure and a safe `fmi3FreeInstance(NULL)`),
lifecycle rejection, argument rejection, `fmi3Discard`, the suppressed-versus-
enabled logging split, the 25 capability rejections (message and callback split),
the 24 absent-typed empty (`fmi3OK`) and non-empty (`fmi3Error`) accessors,
`fmi3SetDebugLogging` valid/invalid, `fmi3Reset` with re-initialization, and
`fmi3GetVersion`. Every observed status and message matches the proved behavior;
0 discrepancies. This is native boundary evidence, not proof authority
(finding F6).

### 3.2 Tensor FMI 3 adapter (`FMI3.TensorAdapter.Contract`), all 75 functions

The tensor adapter reproves the same 75-function coverage through the tensor
family contracts (`TensorAdapterContract.lean:52-157`): `PublicAPI.Covered`,
`TensorAbsentVariables.FamilyContract`, `TensorCapabilityRejection.FamilyContract`,
and the per-function `Tensor*.Contract` lemmas. The earlier DoStep summary below
was stale; its corrected scope is:

| Family | Difference from 3.1 |
|---|---|
| DoStep `fmi3DoStep` | `TensorDoStep.Contract` retains accepted execution, null rejection and off-grid discard, and requires lifecycle, argument, rounding, stop and full-discard products including missing callbacks. Same-table step/helper bindings, prepared literal calls and accepted output/mode observations are mandatory. These increments and the subsequent concrete numerical-table/runtime linkage passed their full gates, as recorded above. Finite-arithmetic outcomes, complete source histories and native correspondence remain open; do not infer complete scalar parity. |
| All others | Same marks as 3.1, discharged by `TensorVersion.contract`, `TensorReset.contract`, `TensorCountQueries.contract`, `TensorNominals.contract`, `TensorSetTime.contract`, `TensorLifecycleModes.contract`, `TensorFloat64.get_contract`/`set_contract`, `TensorContinuousStates.*_contract`, `TensorDiscreteUpdate.contract`, `TensorCompletedStep.contract`, `TensorEventIndicators.contract`, `TensorDiscreteEvaluation.contract`, `TensorFactory.contract`, `TensorFree.contract`, `TensorAbsentVariables.family_correct`, `TensorCapabilityRejection.family_correct`. |

The former count of two open tensor cells is withdrawn: it named already-proved
cases and omitted the remaining DoStep rejection/composition obligations. The
other family marks above are carried forward, not newly re-established here.

**Native instantiation (tensor).** The same all-behavior matrix now runs on the
actual `build/TensorSquare.fmu` (produced by the default CLI's tensor path) from
`tests/fmi3.sh`: the preceding recorded run covered 75/75 functions and 514
behavior cells, the same classes as the
scalar run. This closes the native gap recorded in finding F2 for every class the
tensor adapter shares with the scalar one. Two native observations of note. (i)
The `fmi3DoStep` off-grid discard cell is instantiated natively and returns
`fmi3Discard`, matching its proved suppressed/logged composition. (ii) `fmi3Reset` now conforms
to the scalar adapter and to FMI 3.0.2 (finding F8, closed): after initialization
has run, `fmi3Reset` returns `fmi3OK`, a subsequent `fmi3EnterInitializationMode`
succeeds and a step runs, so the reset instance re-initializes. The matrix carries
no recorded findings; 0 recorded-finding discrepancies and 0 unexpected on both
FMUs.

### 3.3 Scalar C numerical kernel (coarse)

`Rumoca.ArtifactContract` (`Verified.lean:42`) covers the private kernel
`model.c` by execution *behavior*, not by FMI function:

| Behavior | Coverage | Theorem |
|---|---|---|
| Terminating binary64 execution of each sampled call | P | `execution_correct`, `call_termination`, `call_completion` |
| Every emitted behavior is a source behavior and conversely | P | `behaviors`, `compiler_semantic_preservation` |
| Model-exchange derivative and co-simulation step | P | `model_exchange`, `co_simulation` |
| Real-ODE refinement bound | P | `real_solution_refinement`, `ExecutionContract.rounding_error` |
| 64-bit counter safety | P | `counter_safe` |
| Byte identity of the actual `model.c` | checked | `bytes` (kernel `decide`) |
| Native compilation / host ABI / IEEE realisation | external | (trusted boundary) |

### 3.4 Tensor C kernel (coarse)

`IVPEntry.ArtifactContract` (`Tests/TensorCChecks/IVPEntry.lean:268`):

| Member | Coverage | Theorem |
|---|---|---|
| Pointwise IVP program (`initial`, `derivative`, coefficients) | P | `program_correct` |
| Initial-storage entry | P | `initial_call_correct` |
| Derivative-storage entry (`rumoca_rhs`) | P | `derivative_call_correct` |
| Square-Jacobian diagonal entry (`rumoca_square_jacobian_diag`) | P | `jacobianDiag_correct` (`helper_call_correct`, `output_reads`, `output_frame`) |
| Byte identity of each actual fragment | checked | fragment reflexive checks (`tests/tensor-c.sh`) |
| Native heap / header realisation | external | (trusted boundary) |

### 3.5 eFMI artifacts (coarse)

| Artifact | Behaviors proved | Checked bytes | External |
|---|---|---|---|
| Algorithm `model.alg` | lexing, EBNF, GALEC parse/denote, DAE admission, startup/recalibrate/doStep/samples, solve + lifecycle trace refinement | `bytes`, grammars | host scheduler, XML/ZIP/checksums |
| Production C | header contract, startup map, module lowering + render + denote, typed entry, per-method + startup heap behavior, both `CProtocol` trace directions | production C `bytes` | native C compiler, host scheduling |
| Manifest XML | valid/identified/named documents, XML rendering, variable roster, mapped result/status | algorithm/production/content XML `bytes` | full XSD/prose conformance |
| Archive `.efmu` | manifest contract, stored-ZIP `Format.Conforms` transport | member roster, pinned schema resources, archive `bytes` | native C compiler, physical I/O + atomic rename |

---

## 4. Quantifier and non-vacuity review

### 4.1 What is universally quantified, per contract family

- **Scalar C artifact / source-build.** `ArtifactContract` quantifies over all
  finite IEEE inputs and 64-bit counters: `execution : ∀ x n`, `behaviors : ∀ f
  x n b`, `call_termination/completion : ∀ f x n [s]`,
  `real_solution_refinement : ∀ f x n y` (`Verified.lean:50-67`). The
  source-build theorem `Rumoca.CheckedFMI3Files.source_to_build` is an
  existential `∃ a : Artifact input, compile input = .ok a ∧ SourceBuildContract
  …` whose witness is the *actual* compiled artifact (non-vacuity by
  construction, section 4.3).
- **Scalar adapter.** `AdapterContract` is `∃ sigs …` with the signature list
  fixed to the real header; each per-function contract quantifies over heaps,
  prepared pools, headers, objects, literal addresses, loggers, the `signed`
  logging flag, and reason enumerations. `adapter_call_entry` quantifies over
  all convertible argument lists (`FMI3AdapterProofs.lean:297-319`).
- **Tensor adapter.** `TensorAdapter.Contract` quantifies `∀ [StaticLiterals]`,
  `∀ (header : CFenv.Header) (objects) (literals)` for the seven
  runtime-interface functions, and `∀ (E) (prog) (tag)` for factory/release
  (`TensorAdapterContract.lean:63-97`); the symbolic tensor `shape` is a free
  variable, so the bodies never enumerate elements.
- **Tensor C kernel.** `IVPEntry.ArtifactContract` storage contracts quantify
  `∀ [interface] (definitions) {shape} (heap) …` under resolution, header-type,
  separation, readability, non-overflow and `< 2^64` hypotheses
  (`Tests/TensorCChecks/IVPEntry.lean:242-259`).
- **eFMI.** Algorithm quantifies `∀ x n` (samples) and `∀ before after events`
  (lifecycle trace); production quantifies `∀ method heap p state` and both
  `CProtocol` trace directions; archive is existential over the code bundle.

### 4.2 Fixtures and native runs that instantiate the premises

| Fixture | Instantiates | Premises exercised |
|---|---|---|
| `tests/fmi3.sh` + `tests/fmi3.py` | actual `Integrator.fmu` build, `validate`, `info`, me and cs `simulate`, CSV equality `(0,.5)(1,1.5)(2,2.5)(3,3.5)`, source-linked second model | success (me/cs run), argument rejection (`--mode invalid`), discard (`--step 0.5`), missing-FMU rejection, unsupported-profile admission rejection (`DrivenIntegrator` must not replace a valid FMU) |
| `tests/fmi3.py --matrix` on `Integrator.fmu` and `TensorSquare.fmu` (from `tests/fmi3.sh`) | raw FMI ABI over all 75 public functions of both adapters | null handle (all 74 handle-taking functions + factory null + `fmi3FreeInstance(NULL)`), lifecycle rejection, argument rejection (non-finite set, unknown reference, mismatched `nValues`), off-grid `fmi3Discard`, suppressed-versus-enabled logging split, 25 capability rejections (message + callback split), 24 absent-typed empty (`fmi3OK`) and non-empty (`fmi3Error`) accessors, `fmi3SetDebugLogging` valid/invalid, `fmi3Reset` + re-init (re-initialization and a step after reset succeed on both adapters), `fmi3GetVersion`. 75/75 functions, 514 cells per FMU; 0 recorded-finding discrepancies, 0 unexpected (finding F8 closed) |
| `tests/tensor-c.sh` | actual tensor C emission; `verify_tensor_helper` for add/mul/fill/diagonal; `verify_tensor_ivp`; corrupted loop bound and corrupted IVP member rejected | tensor kernel checked byte identity + rejection |
| `tests/efmi-algorithm.sh` | actual `model.alg` vs `UnitIntegrator.alg`; `verify-algorithm` on real source/grammars; LALR engine reuse; invalid-namespace rejection | algorithm `bytes`, grammar identities, generator reuse |
| `tests/efmi-production.sh` | actual `model.efmu`; axiom-audited `source_to_archive`; cached `--check-only efmi-archive` reuse; foreign-identity and failed-tool rejections | production/archive `bytes`, roster, schema resources, cache identity |
| `tests/verification-negative.sh` | mutated `Model.c`, mutated embedded source, renamed model, unapproved-axiom log | the checked byte/source premises and the axiom audit (negative direction) |
| compiler test executable `packages/compiler/Tests/Audit.lean` and the per-package audit files | full kernel-checked axiom closure of every listed root | axiom-audit trust roots (section 5) |

### 4.3 Non-vacuity

The two source-build existentials are witnessed by real compiles, so the
contracts are not vacuously true: `verify_fmi3_build_files` obtains the witness
from `compile (.single sourceName source)` on the actual `Integrator` source
(`FMI3BuildArtifactCheck.lean:37`), and `verify_tensor_fmi3_build_files` from
`compileTensor input` on the actual `TensorSquare` source, pinned to `squareAst`
/ `squareModel` by lexer/parser determinism (`TensorProduction.lean:112-158`).
`compile_complete` / `compileTensor_complete` further show the parse/lower path
is inhabited for every resolvable source, so the `∃ a` is populated rather than
assumed.

### 4.4 Conjuncts no test or fixture instantiates (flagged)

1. **Tensor adapter native coverage (updated).** The default CLI now admits the
   array profile and publishes `build/TensorSquare.fmu`, and `tests/fmi3.sh` now
   runs the all-behavior matrix on it, so every behavior class the tensor adapter
   shares with the scalar one is instantiated natively (75/75 functions, 514
   cells). What remains proof-only for the tensor path is the Lean-internal
   binding of `TensorAdapter.Contract` to specific heaps/headers; the native run
   observes the emitted ABI, not the contract witnesses. (Finding F2, largely
   discharged; F8 closed.)
2. **Scalar and tensor behaviors are now natively instantiated (updated).**
   `tests/fmi3.py --matrix` natively exercises, on both adapters, the classes that
   were previously proof-only: the suppressed and enabled logging split, the 25
   capability rejections (including the FMUState, serialize and deserialize
   functions, which are capability-rejected), the 24 absent-typed accessors (empty
   and non-empty), null handles, lifecycle and argument rejections, and discard.
   This native evidence supplements, and does not replace, the universal proofs;
   the assurance case must still not read the matrix as proof authority.
   (Finding F6.)
3. **Two tensor `fmi3DoStep` behaviors are unproved and unexercised**: the
   off-grid `fmi3Discard` composition and the header-aware floating-environment
   interface (`TensorAdapterContract.lean:36-39`). (Finding F1.)

### 4.5 Premises that could be unsatisfiable (flagged)

These are genuine hypotheses (so the contracts are non-vacuous), but the
guarantee does not extend to inputs that violate them:

- **Finite Jacobian doubling.** `JacobianDiagStorageContract` assumes
  `∀ i, Binary64.Adds values[i] values[i] (.finite result[i])`
  (`Tests/TensorCChecks/IVPEntry.lean:249`): for coefficients whose doubling
  overflows to infinity this premise is unsatisfiable, so the diagonal-storage
  guarantee excludes overflowing Jacobians.
- **Counter and region bounds.** `ExecutionContract.counter_safe` is guarded by
  `n < 2^64` (`Verified.lean:25`) and the storage contracts by
  `region.volume < 2^64` (`IVPEntry.lean:251`); beyond those bounds no guarantee
  is claimed.
- **External binding hypotheses.** `program.externals "floor"/"fegetround"/
  "atomic_exchange"/"atomic_store" = some (…)` (`FMI3AtomicCalls.lean:33-35`,
  `FMI3CSLifecycle.lean:27-30`) are satisfiable only when the importer binds
  these to the modeled implementations; an importer that binds otherwise is
  outside the guarantee. (Finding F4.)

No premise reviewed here is unsatisfiable for *every* input (which would make its
contract vacuous); each excludes a bounded numeric or environmental region that
is recorded above.

---

## 5. Axiom audit summary

The audit mechanism is `ProofAudit.audit` (`packages/verification/ProofAudit/Audit.lean:11`):
`collectAxioms` walks the complete kernel-checked dependency closure of a named
declaration and throws a Lean error unless every axiom is in
`{propext, Classical.choice, Quot.sound}` (`:14`). The `#audit axioms`
command (`:19`) applies it; the identical whitelist is embedded in every
`verify_*` artifact checker (`FMI3BuildArtifactCheck.lean:114`,
`TensorFMI3BuildArtifactCheck.lean:221`, `EFMIArchiveArtifactCheck.lean:78`,
and the per-fragment tensor checks). `scripts/audit-lean.sh` re-checks the
logged axiom lines at the shell boundary, and `tests/verification-negative.sh`
confirms an injected `unapproved_axiom` is rejected there.

The rejection direction is self-tested in
`packages/verification/Tests/AuditChecks.lean`: `True.intro` audits clean, and
`Lean.ofReduceBool` (the native-reduction axiom) is rejected, so
native-reduction proof axioms cannot enter the trusted set.

Audit roots per package (count of `#audit axioms` roots):

| Package | Roots | Audit files |
|---|---|---|
| `backend-fmi3` | 2431 | `Tests/FMI3Audit.lean`, `CallChecks`, `FMI3CallPolicyAudit`, `HistoryChecks`, `MemoryChecks`, `TimeChecks` |
| `backend-c` | 1156 | `Tests/CAudit.lean`, `CCallPolicyAudit`, `TensorAudit` |
| `compiler` | 321 | `Tests/Audit.lean`, `EFMIChecks`, `FMI3SourceCallPolicyAudit`, `SemanticChecks`, `TensorAdapterFixture`, `TensorMetadataFixture` |
| `core` | 317 | `Tests/CoreAudit.lean`, `FiniteChecks`, `TensorChecks` |
| `parser` | 249 | `Tests/ParserAudit.lean`, `LALRChecks`, `LALRFirstChecks`, `LALRSafetyChecks` |
| `backend-efmi` | 129 | `RumocaEFMISchemaCertificates.lean`, `Tests/ProductionChecks` |
| `modelica-parser` | 82 | `Tests/ModelicaParserAudit.lean` |
| `galec-parser` | 31 | `Tests/GALECParserAudit.lean` |
| `sha1` | 17 | `Tests/SHA1Checks.lean` |
| `xml` | 11 | `Tests/XMLChecks.lean` |
| `lsp` | 4 | `Tests/LSPAudit.lean` |
| `verification` | 2 | `Tests/AuditChecks.lean` (accept/reject self-test) |

Total: roughly 4749 audited roots. The eight heaviest axiom audits are each
partitioned into one audit file per source module under a directory beside the
listed library root, which imports them all: `FMI3Audit` and
`FMI3CallPolicyAudit` (`backend-fmi3`), `CAudit`, `CCallPolicyAudit` and
`TensorAudit` (`backend-c`), `Audit` and `FMI3SourceCallPolicyAudit`
(`compiler`), and `CoreAudit` (`core`). Lake elaborates those files as
independent parallel jobs; the library root names and the audited-root set are
unchanged. The keystone roots
for this ledger are `Rumoca.FMI3.sourceBuild_correct`,
`Rumoca.tensorSourceBuild_correct`, `Rumoca.artifact_correct`,
`Rumoca.compiler_semantic_preservation`, and the eFMI
`source_to_archive` root; the `verify_*` checkers additionally audit the actual
`source_to_build` / archive theorems that bind those to real bytes.

---

## 6. Findings and closure criteria

Each finding is tagged with the roadmap package that owns its closure. This
ledger ticks nothing.

- **F1 (K05, F01).** The formerly missing tensor off-grid discard and
  floating-environment header coverage are present in `TensorDoStep.Contract.discarded`
  and the header-quantified `TensorAdapter.Contract`. Lifecycle rejection now also
  appears in the mandatory tensor and constant step contracts as `lifecycleSilent`
  and `lifecycleLogged`; the latter retains external callback effects and the
  no-outcome case. The combined follow-up adds `lifecycleMissing` and binds the
  actual step/helper definitions to the certified adapter table. The initial
  targeted audits passed; the preliminary full gate in
  `build/step-lifecycle-full-gate.log` was deliberately stopped (exit 143) before
  integrating those follow-ups and the explicit logger null comparison.
  Combined targeted checks passed (`build/logger-contract-package-v2.log`);
  `build/logger-contract-full-gate.log` later failed when the actual tensor
  certificate attempted an unavailable signature equality decision procedure.
  The repaired tensor and constant actual-file rechecks passed; each native
  matrix passed 75/75 functions and 526 cells with zero discrepancies. The required
  full gate passed on 2026-09-21 (exit 0;
  `build/logger-contract-full-gate-v2.log`), including the three production FMI
  matrices and scalar/tensor eFMI actual-artifact and mutation checks. A subsequent
  proof-only increment integrates mandatory missing-output and invalid-input
  contracts; package validation passed (`build/step-argument-contract-package.log`,
  exit 0, 4,045 jobs) and its required full gate passed on 2026-09-21 (exit 0) in
  `build/step-argument-contract-full-gate.log`, with unchanged implementation
  fingerprints and all three 75-function/526-cell matrices passing. Retained FMU
  source-build audits use only the permitted axioms; scalar/tensor eFMI actual
  artifacts and mutation controls passed. A subsequent proof-only increment adds
  mandatory `roundingRejected`, `stopRejected` and `discardRejected`, covering
  non-nearest rounding, stop limits, nonprogress/nonfinite-next-clock and
  off-grid/over-bound discard with all three logging cases. Its 22 audit roots
  passed scratch rehearsals and integrated package validation (exit 0, 3,795 jobs,
  `build/step-numeric-contract-package.log`). Its required full gate passed on
  2026-09-21 (exit 0, observed 19:22:37 UTC) in
  `build/step-numeric-contract-full-gate.log`, with unchanged implementation
  fingerprints. All three 75-function/526-cell FMI matrices and scalar/tensor
  eFMI artifact/mutation controls passed. Retained FMU source-build audits use
  only the permitted axioms; evidence and artifact identities are in
  `build/step-numeric-contract-checkpoint.md`.
  The older `discarded` field still assumes `StepGuards.Progress`; the new
  `discardRejected` also covers that earlier branch without floor premises.
  The next combined proof-only increment now requires successful preparation and
  six prepared logged-rejection calls per profile, deriving exact literal
  addresses/contents at callback entry. Existing accepted execution products
  require three false Boolean outputs and selected-mode preservation on the
  same final heap, with all earlier premises and guarantees retained. Independent
  review, isolated owner compilation and 58 selected audits passed. Integrated
  package validation passed all 4,055 jobs (exit 0) in
  `build/step-composition-package-v3.log`, including all 39 new roots. Its
  required full gate passed (exit 0, observed 2026-09-21 at 20:47:09 UTC) in
  `build/step-composition-full-gate-v3.log`; its frozen inputs and artifact evidence
  are recorded in `build/step-composition-checkpoint-v3.md`. The subsequent
  numerical-linkage checkpoint above additionally establishes the mandatory
  same-source numerical table and concrete runtime composition. Full step coverage
  still needs finite-arithmetic outcomes and complete source/clock histories.
  Literal installation/initial frames, external callbacks and native correspondence
  stay explicit; these increments do not close the whole step or MISRA finding.
- **F2 (K05, F02).** *Native evidence added.* The default CLI now admits the
  array profile and publishes `build/TensorSquare.fmu`, and `tests/fmi3.sh` runs
  the all-behavior matrix (`tests/fmi3.py --matrix`) on it. The latest recorded
  numerical-linkage gate passed 75/75 functions and 526 behavior cells;
  the preceding matrix covered 514 cells.
  The tensor FMU native fixture paralleling `tests/fmi3.sh` now exists.
  *Remaining:* the native run is boundary evidence, not proof of native header
  correspondence, complete numerical outcomes or source histories (F1).
  The reset divergence F8 was surfaced by this run and is now closed (the
  tensor reset restores the Instantiated state; re-initialization succeeds).
- **F3 (K03, K05, N01).** Finite-arithmetic outcome premises are conditional:
  `JacobianDiagStorageContract` excludes coefficients whose doubling overflows,
  and counter/region guarantees are bounded by `< 2^64`. *Closure:* record the
  excluded numeric domain in `standards-review.md` and either prove the
  saturation/overflow behavior or accept the bound explicitly in the R1 ledger.
- **F4 (K05).** The external bindings `floor`, `fegetround`, `atomic_exchange`,
  `atomic_store` and the host logger callback are universally quantified
  assumptions about `program.externals`; no native gate validates the importer's
  actual bindings. *Closure:* record the importer/runtime binding obligations in
  the trust-boundary section of `docs/verification.md`.
- **F5 (K05, C01).** The machine-compilation / host-ABI / IEEE-realisation
  boundary (`Verified.lean:7-10`) is the largest external assumption for both C
  kernels and is stated but not independently reviewed against a pinned
  toolchain. *Closure:* K05 independent review of the authored C/IEEE semantics
  against the pinned toolchain, with CompCert/Flocq as design references only.
- **F6 (K05, A02).** *Native evidence added.* The all-behavior matrix
  (`tests/fmi3.py --matrix`, run from `tests/fmi3.sh` on both `Integrator.fmu` and
  `TensorSquare.fmu`) now instantiates natively, at least once per adapter, the
  logging split, the 25 capability rejections (FMUState/serialize/deserialize
  included), the 24 absent-typed accessors, null handles, lifecycle and argument
  rejections, and discard: 75/75 functions, 514 cells, statuses and messages
  matching the proved behavior. *Closure:* the R1 assurance ledger states that
  these behaviors are proof-established and additionally native-instantiated as
  boundary evidence, without reading the native matrix as proof authority.

- **F8 (K05, A02). CLOSED.** *Surfaced by the native matrix; fixed with proofs.*
  The tensor adapter's `fmi3Reset` now restores exactly what the scalar reset
  restores, returning the instance to the state directly after `fmi3Instantiate`
  (FMI 3.0.2, `fmi3Reset`). The body (`Rumoca.FMI3.TensorReset.bookkeepingTail`)
  keeps the symbolic zero-fill of the state region and additionally resets the time
  base and the lifecycle bookkeeping cells `timeMin`, `eventTime`,
  `lastCompleted`, `stop`, `stopDefined` to zero and writes the lifecycle `mode`
  cell to Instantiated, mirroring the scalar `Reset.tail`. Proof: the reset runs to
  the result heap `finalHeap` in `TensorReset.reset_reaches`/`reset_behaviors`,
  whose bookkeeping tail is discharged universally in the post-fill heap by
  `TensorReset.bookkeeping_reaches`; `TensorReset.reset_mode_instantiated` proves
  the `mode` cell reads Instantiated after reset (`Mode.instantiated.code`), which
  is the guard input `fmi3EnterInitializationMode` requires; `reads_initialization`
  keeps the state region at the prepared fixed-zero fill and
  `preserves_other_instances` keeps every other pool instance untouched. The
  `mode`-reads-Instantiated conjunct is carried by `TensorReset.Contract`
  (`reinitializes` field, discharged by `TensorReset.contract`) into
  `TensorAdapter.Contract`. *Native evidence:* with the allowlist removed
  (`tests/fmi3.py` `KNOWN_DISCREPANCIES = {}`), the all-behavior matrix over the
  regenerated `TensorSquare.fmu` reports "75/75 functions, 514 behavior cells
  exercised, 0 recorded-finding discrepancies, 0 unexpected": after a full
  initialization, `fmi3Reset` returns `fmi3OK`, a subsequent
  `fmi3EnterInitializationMode` succeeds and a step runs, so the reset tensor
  instance re-initializes exactly as the scalar adapter's does.
- **F7 (K04, K05, eFMI E05–E06).** eFMI archive conformance is checked against a
  pinned schema roster and the stored-ZIP format only; full XSD/prose-standard
  conformance and the external C compiler are external. *Closure:* eFMI
  E05/E06 standards-review closure.

**Coverage summary.** Contracts: 10 mandatory actual-artifact contracts
(section table). Conjuncts: scalar source-build 6 (expanding to 14 numerical +
32 adapter + 4 recipe); tensor source-build 7; scalar C 14; tensor C 5; eFMI
algorithm 11, production 6 groups, manifest 3 groups, archive 3. Premises by
class: one checked byte-identity per emitted file plus checked grammar/roster/
schema identities; all semantic content proved; the machine-compilation, header,
library-binding, archive-I/O and external-standard layers external. Functions by
coverage: 75/75 covered on the scalar adapter with no open cell; 73/75 fully
covered on the tensor adapter with 2 open `fmi3DoStep` cells. Native
instantiation: the all-behavior matrix (`tests/fmi3.py --matrix`, from
`tests/fmi3.sh`) exercises 75/75 functions and 514 behavior cells on each of
`Integrator.fmu` and `TensorSquare.fmu`, matching the proved statuses and
messages with 0 recorded-finding discrepancies and 0 unexpected on both FMUs; the
former reset divergence (finding F8) is closed, so the tensor `fmi3Reset` restores
the Instantiated state and a reset tensor instance re-initializes. Axioms: the only
approved roots are `propext`, `Classical.choice`, `Quot.sound`, enforced at
roughly 4749 audited roots and by each `verify_*` checker.
