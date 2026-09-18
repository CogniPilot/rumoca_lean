# Trust and premise ledger (K05)

This ledger records, for every mandatory actual-artifact contract in the frozen
subset, the theorem quantifiers, the classification of each premise, the
all-behavior coverage of the emitted interfaces, the non-vacuity evidence, and
the axiom-audit trust roots. It is the premise and trust ledger required by
roadmap package K05. It ticks nothing: it is a review record, not a closure
claim.

Premise classes used throughout:

- **proved** — discharged by a Lean theorem over the universally quantified
  model; the discharging theorem is named.
- **checked** — decided by a fixed artifact checker on the *actual* bytes of the
  emitted file (a `verify_*` elaborator or `#audit`), reducing by `decide`,
  `rfl`, `Eq.refl`, or a certificate that reads the real file; the check is
  named. Candidate bytes are never proof authority: the checker only rejects.
- **external** — assumed of the platform, importer, toolchain, headers, or
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
| `Rumoca.TensorSourceBuildContract` | `TensorProduction.lean:211` | `Rumoca.tensorSourceBuild_correct` `TensorProduction.lean:237` | `verify_tensor_fmi3_build_files` (`Tools/CheckTensorFMI3Build.lean`) |
| `FMI3.TensorAdapter.Contract` | `TensorAdapterContract.lean:52` | `FMI3.TensorAdapter.render_contract` `TensorAdapterContract.lean:160` | via `TensorFMI3AdapterCertificate.certify` |
| `IVPEntry.ArtifactContract` (tensor C) | `Tests/TensorCChecks/IVPEntry.lean:268` | `IVPEntry.artifact_correct` `:271` | `verify_tensor_ivp` (`Tests/TensorCChecks/ArtifactCheck.lean`) |
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
is `decide +kernel` (`:62-64`) — **checked**; the identity of `mdTree` with the
actual `modelDescription.xml` bytes is **checked** via `metadata_bytes`
(`:57-58`).

### 1.5 `adapter : AdapterContract a adapter` (`:19`)

`AdapterContract` (`FMI3AdapterProofs.lean:61`) is an existential over the FMI
signature list with 32 conjuncts. It is discharged by the adapter certificate
`FMI3AdapterCertificate.certify` (`FMI3BuildArtifactCheck.lean:74`), which runs
`adapter_correct` (`FMI3AdapterProofs.lean:121`).

- **checked** — the byte identity `Runtime.render a.solve.prepareFMI3 sigs =
  adapter` (`:66`) is established by `adapter_chars` (`:47`), which binds the
  independently read `fmi3.c` bytes to the concatenation of the per-function
  renders; the signature list `sigs` itself is **checked** to be the actual
  `fmi3FunctionTypes.h` signatures via `FMI3.Header.signatures header`
  (`FMI3BuildArtifactCheck.lean:73`); `CTree.Preprocessing.Stable adapter.toList`
  (`:64`) is proved over those checked bytes.
- **proved** — the remaining 30 conjuncts: `Nodup` of names (`:62`),
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
- **external** — native ABI and call convention, whole-C preprocessing/macro
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
The XML validity is `certifyValidity` (`:59`, `decide`) — **checked**; the
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
are stated over an arbitrary event program `prog` and tag (`:94-97`) — the
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
`< 2^64` and non-overlapping — the native heap and header realisation are
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

- **checked** — `bytes : a.productionSource = .ok c` (the actual production C
  member reduces to the lowered module render; `production_source_is_unit`
  `:55` fixes the module).
- **proved** — `algorithm_contract` (the AlgorithmContract), `algorithm_names`,
  `header : CHeader.Contract c`, `startup_map : Production.StartupMap.Contract`,
  and the `target` existential: the lowered `Production.Module`, its render, its
  `CSyntax.Denotes`, the typed parameter/return conversions, `Metadata.Contract`,
  the per-method heap-behavior equivalence, the startup-initialization behavior,
  and both directions of the `CProtocol` trace refinement.
- **external** — the physical C compiler, host scheduling, and the archive/XML
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

- **checked** — the eFMU member roster (`:21`), each pinned schema resource
  (`:24`, byte compare against the pinned release), and the actual archive bytes
  (`String.fromUTF8?` on the read members, `:27`).
- **proved** — `ManifestContract` and the ZIP `Format.Conforms` transport.
- **external** — the external C compiler, full XSD/prose-standard conformance,
  and the physical archive file I/O and atomic rename (`:9`,
  `EFMIExport.lean:7`).

**Section 2 totals.** Tensor build 7 conjuncts; scalar C 14 fields; tensor C 5
conjuncts; eFMI algorithm 11 fields, production 6 groups, manifest 3 groups,
archive 3 conjuncts. In every contract the emitted-file byte identity is the
checked premise, the semantic content is proved, and the machine
compilation / archive I/O / external-standard layer is external.
