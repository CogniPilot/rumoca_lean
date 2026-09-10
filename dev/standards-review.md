# MLS, FMI and eFMI compliance review — 2026-09-10

The current artifacts are **not ready for a full standards-compliance claim**.
This review reproduced two source-FMU integration failures, found an omitted
eFMI error-status mapping and an FMI lifecycle mismatch, and retained two
initialization restrictions as unresolved policy questions. These issues take
priority over the next tensor/FMI implementation round. No grammar, compiler
semantics, proof contract or production artifact was changed for this review.
The original findings below retain their reviewed revision and repair evidence.
The stage checklist and MLS follow-up make this a recurring three-standard
review, rather than a one-time backend inspection.

## Required review at every spiral stage

Before extending the grammar or admitting a development profile to production,
complete the following record for the **entire currently admitted subset**.
Reuse unaffected evidence only after checking its dependencies; review changed
interactions across all three standards even when no grammar file changed.

| Required record | Evidence needed to close the stage |
| --- | --- |
| Scope and identity | Source revision, production entry points, exact source/GALEC EBNFs, admitted and rejected forms, deliberate extensions, and the actual artifacts reviewed. |
| Normative baseline | MLS, FMI and eFMI versions; relevant clauses; pinned header/schema identities. Upstream Rumoca and compliance tools are references, not normative authorities. |
| MLS coverage | Lexical/syntactic admission, resolution, types and shapes, equation meaning, initialization, numeric interpretation and diagnostics. Keep `jacobian` explicitly identified as an extension. |
| FMI coverage | Both advertised ME and CS interfaces: metadata, initialization, legal and rejected calls, time/solver policy, errors/logging, storage/lifetime, source builds and archive contents. |
| eFMI coverage | GALEC semantics and methods, sample-period policy, Production C execution, logical mappings/status, correlated manifests/checksums, archive layout and coding-guideline obligations. |
| Proof correspondence | For each applicable clause: independent specification, lowering/target theorem roots, actual-file/archive proposition and any remaining external assumptions. A theorem about an emitter's own policy does not establish that policy's conformance. |
| Boundary evidence | Required `lake test` outcome and artifact identities, plus existing schema/importer/native checks where tools or interfaces lie outside Lean. Record checker limitations explicitly. |
| Decision | Carry forward every open finding with closure criteria. Close applicable findings before growth. Record a reason for each excluded clause; an unproved advertised behavior cannot be marked inapplicable. |

The stage is **open** if any applicable compliance finding or required compiler
proof/artifact obligation remains unresolved. A passing schema, importer or CI
run cannot change that decision by itself. This is a review gate, not an
automated claim that Lean has formalized the prose standards. Use universal
proofs for compiler properties and keep tests to the existing external boundaries.

## Current unit-stage follow-up

Reviewed implementation: `df382d05287449d2c987f7414482b4edb562c28f`.
The normative baselines are [MLS 3.7](https://specification.modelica.org/maint/3.7/MLS.html),
[FMI 3.0.2](https://fmi-standard.org/docs/3.0.2/) and the pinned
[eFMI 1.0.0 Beta 1 archive](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
The eFMI archive identity is recorded below; this is not a final eFMI 1.0 claim.

Production accepts a single unmodified `Real` declaration and `der(x) = 1`,
with matching model/end names and a derivative reference to that declaration.
The EBNF also contains frozen development profiles; their recognition does
not imply production acceptance. Reviewed EBNF SHA-256 identities are:

| File | SHA-256 |
| --- | --- |
| `packages/modelica-parser/grammar/Modelica.ebnf` | `90be2d4fe36634a43af1c0c57c394054468b8ebfc1c08c572f6bdfc7cb412b0e` |
| `packages/galec-parser/grammar/GALEC.ebnf` | `0cfa1a87ac98a207d6fd05628414763e0d4b7640641d6c262f246cecae40ab7a` |

This is the initial clause map for S01, not closure of the full source-semantics
review. A restriction of the supported language and a mismatch for accepted
input are different findings.

| Applicable obligation | Implementation/proof correspondence | Review result or remaining obligation |
| --- | --- | --- |
| MLS §§2.1–2.4 and A.1: ordinary identifiers, keywords, whitespace and the integer literal `1`. [Lexical clauses](https://specification.modelica.org/maint/3.7/lexical-structure.html) | [Lexer](../packages/modelica-parser/ModelicaParser/Lexer.lean): `lex_correct` characterizes maximal-munch scanning; `reserved` includes the keywords and four protected predefined type names. | Reviewed for the ASCII restriction. Comments, quoted identifiers and other literal forms remain excluded; the theorem is about the authored lexical rules. |
| MLS A.2.1, A.2.2, A.2.4, A.2.6–A.2.7: one model, declaration and equality equation. [Concrete syntax](https://specification.modelica.org/maint/3.7/modelica-concrete-syntax.html) | [ParserProofs](../packages/modelica-parser/ModelicaParser/ParserProofs.lean): `parsed_in_ebnf`; [Compiler](../packages/compiler/Rumoca/Compiler.lean): `compile_complete` for the resolved unit token shape. | Generated-grammar membership is proved. Independent metalanguage/grammar correspondence remains P02; there is no full MLS parser-completeness claim. |
| MLS §§8.2–8.3.1: equation lookup and compatible equality operands. [Equation clauses](https://specification.modelica.org/maint/3.7/equations.html) | [AST](../packages/modelica-parser/ModelicaParser/AST.lean): `Resolved`; [LocatedProofs](../packages/modelica-parser/ModelicaParser/LocatedProofs.lean): `resolved_references`, `resolve_error_locations`. | The derivative must name the one declared state; failed resolution has exact occurrence/declaration spans. General scopes are excluded. Record the literal-Integer-to-Real interpretation explicitly in S01. |
| MLS Operator 3.12: `der` is the time derivative of the continuous Real operand. [Operator clause](https://specification.modelica.org/maint/3.7/operators-and-expressions.html) | [Source](../packages/compiler/Rumoca/Source.lean): `Solves`, `trajectory_derivative`; [Behavioral](../packages/compiler/Rumoca/Behavioral.lean): `lowering_chain_behavior_correct`. | The ideal `x₀ + t` trajectory and unit derivative are proved. This does not give finite storage semantics or choose an initial value. |
| MLS §4.9.1: finite stored Real values. [Real type](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html) | [Encoding](../packages/core/RumocaCore/Real/Encoding.lean): `finiteEncodingEquiv`; [Verified](../packages/compiler/Rumoca/Verified.lean): `compiler_semantic_preservation` and `ArtifactContract.real_solution_refinement`. | Binary64 profile and rounding refinement are proved under the documented C/IEEE assumptions. S01/N01 still require reviewed correspondence; unbounded mathematical trajectories are not stored Real values. |
| MLS §8.6 and §4.9: initialization and fallback selection; FMI initialization metadata; eFMI Startup. | Source takes an external finite initial value; [FMI metadata](../packages/backend-fmi3/RumocaFMI3/Metadata.lean) supplies a zero start; [GALEC](../packages/core/RumocaCore/GALEC/IR.lean) selects zero in Startup. | **Open SR08/S01:** justify and compose these policies, including any required diagnostic. Do not infer an initial equation from the derivative equation. |
| FMI §§2.3–2.5, Chapters 3–4: common lifecycle, ME/CS, metadata and artifacts. [FMI specification](https://fmi-standard.org/docs/3.0.2/) | Existing [FMI contracts](fmi3/contracts.md), source-build certificate and selected public-call theorems. | SR01–SR02 corrections are checked. SR04–SR05 and SR07 remain open; selected calls and numerical-file proofs do not certify the complete adapter/archive. |
| eFMI Chapters 2, 3 and 5: container, Algorithm Code and Production Code. [Beta 1 specification](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip) | [EFMIArchiveProofs](../packages/compiler/Rumoca/EFMIArchiveProofs.lean): `compile_archive_verified`, retaining code, method, mapping and manifest contracts. | SR03's status correction is checked. SR06–SR07 and the SR08 cross-standard initialization review remain open. |

**Evidence checkpoint:** the required full local gate passed at this revision
in `build/diagnostic-locations-full-gate.log`, including both FMI interfaces,
the actual eFMU archive theorem, extracted manifests and mutation controls.
Both gates retain their successful archives; reviewed SHA-256 identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `955258912a6037fe0c37bd243bc4b2e6a872cad9d2b1b618d89e6dea22d252f0` |
| `build/Integrator.efmu` | `6c92cdd9e8beea6e1bef21349a6eb456514960a734d3f1911db664056fa9047f` |

The [hosted run for this revision](https://github.com/CogniPilot/rumoca_lean/actions/runs/34524473640)
also passed. **Stage decision: open; grammar growth is blocked.**

### C literal-printer increment: standards impact

The subsequent shared-printer correction is tracked under C01/F03 in
[the roadmap](roadmap.md). It escapes question marks and proves exact literal
bytes after the selected C11 preprocessing rewrites. MLS source admission,
resolution, equation semantics and both EBNFs are unchanged. The FMI impact is
its emitted literals for version/token/category/error handling; correct literal
printing is a prerequisite for complete call proofs, not their replacement.
The current eFMI Production C profile contains no string expressions; its
GALEC method, mapping and initialization obligations remain the same.

The C package audit and disposable native reproduction pass. The complete gate
for this increment is tracked in `build/c-string-printer-full-gate.log`; it
includes both artifact paths and now records their SHA-256 identities. The
earlier snapshot's artifact hashes must not be reused for this run. No SR04–SR08
or whole-adapter obligation is closed by the literal theorem, and this is not
a new completed spiral stage.

## Original FMI/eFMI snapshot and evidence

Reviewed source revision: `2e53e6629cbc5053711c059fd87135e4b88e02a1`.
The production profile remains one state with `der(x) = 1`. The development
array/Jacobian kernels have separate proofs; the production CLI still rejects
those models. This review does not establish conformance for that future slice.

Normative references are [FMI 3.0.2](https://fmi-standard.org/docs/3.0.2/)
and [eFMI 1.0.0 Beta 1](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
The official [eFMI resources page](https://www.efmi-standard.org/resources/)
still identifies Beta 1 as a release candidate. Its downloaded complete
archive has SHA-256
`da5caf207aca412b5601cafaaf72d4e613d1c78964e3f39afc6a5a3d06281a89`.
The prose and schemas in that archive are the authority; the checker is
additional evidence, not the definition of the standard.

Generated artifacts were snapshotted before the ongoing full gate could
replace them. The relevant emitter sources were unchanged at the reviewed
revision. Artifact identities are:

| Snapshot | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `c50dbceb8202988df9fe38f159187af8a994eafb9edf8da33ad3edea62342438` |
| `build/Integrator.efmu` | `66104a67886d39f70507220c21586347928d1ab82e541ad3e6de6ed9695c3dbf` |

Local evidence is under `build/standards-review/`: `artifacts.json` records
inventories, `probe.py` and `probe-results.json` record the native/source/XML
experiments, and `checker/` records independent checker runs. These are
disposable review experiments, not an added permanent test suite. The results
and reproduction details below remain useful if `build/` is cleared.

## Findings

P1 means a release or integration blocker to repair before backend expansion.
P2 means a smaller interface defect or a policy question requiring resolution.
An evidence gap is distinguished from a demonstrated runtime failure.

### SR01 — P1: source build metadata omits the math-library dependency

[Metadata.buildDescription](../packages/backend-fmi3/RumocaFMI3/Metadata.lean)
lists `model.c` and `fmi3.c` with C11, but no library dependency. The adapter
calls `fegetround`. [Package.archive](../packages/backend-fmi3/RumocaFMI3/Package.lean)
adds `-lm` outside that metadata, as does
`test_sources_rebuild_without_lean` in [the existing integration check](../tests/fmi3.py).
The packaged HTML tells a human to link libm; an importer using only the build
description does not receive that instruction.

**Reproduced:** compiling the listed sources into a shared object without an
extra library succeeds on the current Linux toolchain, but a standalone
`dlopen(..., RTLD_NOW | RTLD_LOCAL)` executable fails with
`undefined symbol: fegetround`. The same executable loads the shipped binary.
The loader links only libdl, avoiding accidental resolution through Python's
already-loaded math library. All other numerical compiler flags were retained.

FMI §2.4.10 makes the build configuration responsible for the required compile
and link information. The missing library is a concrete source-import defect;
it does not mean the shipped binary fails to load.
See [Build Configurations](https://fmi-standard.org/docs/3.0.2/#BuildConfiguration).

**Close with:** an explicit supported-platform build description that includes
the required library and floating-point compilation profile, correlated with
the packaged build. Reuse the source-rebuild check, deriving dependencies from
the XML rather than hard-coding the producer's missing flags. Bind the declared
configuration to the same artifact contract. Native linking remains a tested
boundary; do not describe compiler flags as a machine-code proof.

**Repaired for the declared source profiles:** shared Linux/GCC recipes now drive both the XML and
native argument list. `Build.ArtifactContract` independently decodes each
platform's declared compiler, options, sources and math dependency and binds
the actual XML characters. `FMI3.SourceBuildContract` retains the complete
numerical C contract as a conjunct. Six new audit roots pass in
`build/fmi-build-package.log`; the required full gate passed in
`build/fmi-build-full-gate.log`. The existing rebuild now consumes the published
XML and resolves symbols in a separate process, avoiding Python's ambient
libm. The actual-file, official-schema, native and mutation checks pass in
`build/fmi-build-artifact-gate.log`. The actual FMI adapter/model-description/archive
capstone remains open.
The checked FMU has SHA-256
`c3019d6e316b65f8de3a279d48b66276433cbec151ac566322b46af37337d70f`.
[CI for f1ce838](https://github.com/CogniPilot/rumoca_lean/actions/runs/34502115582)
also passed.

### SR02 — P1: two source FMUs collide at the numerical C symbols

[C.render](../packages/backend-c/RumocaC/Codegen.lean) exports `rumoca_rhs`,
`rumoca_step` and `rumoca_sample` with external linkage. The
[FMI adapter](../packages/backend-fmi3/RumocaFMI3/Runtime.lean) refers to those
unprefixed names. FMI API prefixing changes none of them. Metadata also uses
the fixed model identifier `RumocaModel` for every source model.

**Reproduced:** compile the two adapter copies with distinct
`FMI3_FUNCTION_PREFIX=A_` and `B_`, compile their numerical members separately,
then combine the four objects with `cc -r`. Linking fails with three multiple
definitions, one for each numerical symbol. Distinct FMI API prefixes therefore
do not suffice to compose these generated source packages in one executable.

FMI §2.4.10 recommends minimizing exported symbols to prevent such collisions.
This is an embedded/source-integration defect, not a claim that every
separately loaded binary FMU is invalid.
See [source-file linkage guidance](https://fmi-standard.org/docs/3.0.2/#BuildConfiguration).

**Close with:** private numerical helpers in a single integration translation
unit, or a consistently namespaced numerical interface. Preserve the shared
backend's Solve-only ownership and certify the chosen declaration/name
transformation. Account for the model identifier and helper namespace together.
Keep one source-link boundary check; do not duplicate numerical test matrices.

**Repair in progress:** the shared C printer, independent declaration grammar,
statement tokens and complete existing compiler contract now support external
and `static inline` internal linkage. FMI compiles one `fmi3.c` translation
unit which includes the certified private `model.c`. The numerical behavior,
termination and rounding obligations remain unchanged. A parsed model name
produces the valid C identifier `Rumoca_` followed by that name; the map is
proved injective for distinct names. This does not promise globally unique
identifiers for unrelated artifacts with the same model name.

Build XML and ME/CS metadata use that identifier; the actual adapter begins
with its `FMI3_FUNCTION_PREFIX` and private-kernel include. The producer uses
the official header's `FMI3_OVERRIDE_FUNCTION_PREFIX` when compiling the
unprefixed binary ABI, as specified by [FMI §2.2.2](https://fmi-standard.org/docs/3.0.2/#header-files-and-naming-of-functions).
`FMI3.SourceBuildContract` adds actual XML identity observations and an exact
source-prefix fragment to the internally linked numerical contract. The
adapter remainder, preprocessing, native linking and complete archive remain
outside that proposition; the fragment is not a proof of the entire adapter.

Thirteen new roots and the generalized existing compiler/C roots pass the
unchanged axiom audit in `build/fmi-linkage-package.log`. The actual-file gate
caught a Lean stack overflow while certifying the 45 KB adapter prefix equality,
before publication. The fixed file reader now quotes all independently read
characters in bounded blocks. `sourcePrefix_of_chars` derives the unchanged
string-decomposition contract from the checked prefix; the trusted input
encoding uses `String.ofList` of those actual characters. No native equality
check authorizes acceptance, no character is omitted, and the theorem uses the
same axiom whitelist. The actual-file certificate passes in
`build/fmi-prefix-certificate.log`. The integrated importer and native checks
pass, including two actual source FMUs rebuilt from their own XML recipes,
only their distinct FMI APIs exported, and fresh-process symbol resolution.
A changed source prefix is rejected before native compilation, and a failed
native build preserves the existing FMU. The complete targeted gate passed in
`build/fmi-linkage-artifact-gate.log`. The required full local gate passed in
`build/fmi-linkage-full-gate.log` at `efb5c8030b807822fab69ed7817b321835be1a95`.
Its checked FMU has SHA-256
`780186d9d0694b2da60d06e55e55c4a8100d2fafca86b2198026b9adc21902ea`.
[CI for efb5c80](https://github.com/CogniPilot/rumoca_lean/actions/runs/34509004071)
also passed. This closes the checked source-linkage correction;
the broader FMI capstone remains open.

### SR03 — P1: eFMI status returns have no logical error-status mapping

[Manifest.algorithm](../packages/backend-efmi/RumocaEFMI/Manifest.lean)
declares `ErrorSignalStatus id="ERROR_Status"`. Each Production C function
declares an `EfmiStatus` return (`CR_Startup`, `CR_Recalibrate`, `CR_DoStep`).
However, `logicalData` maps only `AV_State` and `AV_Clock` through the instance
parameters. **The actual Production manifest has zero references to
`ERROR_Status`.** A consumer cannot identify the error-status result through
that declared anchor.

Beta 1 §3.1.4 defines this anchor for derived-code status access; §3.2.5 §1.6
defines the 32-bit error encoding. §5.1.5 specifies logical-to-physical mappings.
The omission matters even when the successful unit profile always returns zero.
See the [official Beta 1 specification](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).

The current [MappedResult](../packages/backend-efmi/RumocaEFMI/ManifestProofs.lean)
proves that execution returns zero and that declared state/clock mappings read
the right values. It **does not prove that the status is discoverable through
the XML anchor**. The [compiler manifest contract](../packages/compiler/Rumoca/EFMIManifestProofs.lean)
inherits this omission. XML schema validation and the official checker's deeper
checks both accept the manifest, illustrating the missing semantic obligation.

**Close with:** a decoded status mapping for every block-interface method,
connected to its actual declared C result and Algorithm Code anchor. First
resolve the Beta 1 representation of a return-value reference against the
schema/prose; do not invent an unsupported XML element. Prove uniqueness,
reference/type validity and observation of the executed status. Strengthen the
existing manifest and complete-archive contracts in the same change, with one
missing/redirected-status mutation. No new GALEC error language is needed for
the zero-status unit profile.

**Repaired for the unit profile:** the [status correction](efmi.md#error-status-mapping-correction)
implements a mapped instance field and proves its agreement with each method
result, including uninitialized Startup storage. The nine new audit roots,
native C observations and three official schemas pass. The required full gate
passed in `build/efmi-status-full-gate.log`, including the actual archive
certificate and redirected-status rejection. The checked eFMU has SHA-256
`712a9819677fad8fef65a672fffbbe8ca038540126a6d56fc2cd2071e63ed646`.
[CI for feb57a9](https://github.com/CogniPilot/rumoca_lean/actions/runs/34499145712)
also passed.
The reviewed snapshots above describe the earlier artifact that exposed the
omission. Broader eFMI compliance and release obligations remain open.

### SR04 — P2: nominal-state access is admitted before initialization

[Lifecycle.permittedModes](../packages/core/RumocaCore/FMI3/Lifecycle.lean)
includes `Instantiated` for `getNominals`. Its `Reference.Allowed` predicate
includes the same extra case. Thus `allowed_correct` cannot expose this
specification mismatch.

**Reproduced:** immediately after ME instantiation,
`fmi3GetNominalsOfContinuousStates(instance, &value, 1)` returns `fmi3OK` and
writes `1.0`. FMI lists this call in Initialization, Initialized and Terminated;
it is absent from Instantiated. The status rules require Error for detected
invalid-state calls. See [common states](https://fmi-standard.org/docs/3.0.2/#common-state-machine)
and [return statuses](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions).

**Close with:** correct the independently reviewed lifecycle predicate and
generated guard together, retain the generalized guard proof, and cover this
rejection through the existing error/lifecycle contract. A small addition to
the existing ABI lifecycle check is sufficient at the native boundary.
State-count and event-indicator-count queries are explicitly listed in
§2.3.2's Instantiated calls; their separate `getCounts` rule is retained.

**Correction in progress:** the table and independently reviewed predicate
now exclude Instantiated specifically for nominal queries. The core theorem
`nominals_reject_instantiated` feeds the existing general guard proof.
`ErrorBodies.nominals_reject_run` proves that the actual generated body reaches
the failure call before reading or writing output storage, preserving the whole
heap. `nominals_reject_reaches` carries that result into the typed C call machine.
The existing ME lifecycle test now checks both logging settings, unchanged
output on rejection, final observations and reset/reinitialization.

`ErrorBodies` also proves the actual error helper's mode write and logging
dispatch for both logging branches, the exact callback arguments, and complete
body-entry termination/frame when logging is disabled. It does **not** execute
an enabled callback or bind the helper's string parameter. Those obligations
prevent composition into a complete public failed-call theorem. The generated
nominal query bytes are not yet covered by the numerical/prefix file contract.
SR04's full proof closure therefore remains open despite the corrected guard.

The generic `CBodyEmbedding` proof reuses successful memory-body runs in the
typed tensor-call machine. Instantiating its scope check exposed a nested
`Instance *m` declaration in SetFloat64's empty-array branch. `CLoops` explicitly
rejects nested declarations because it lacks C block scopes. The initial FMI bridge
excluded that body; no scope check was relaxed. Public array-parameter
adjustment, string argument conversion and indirect callbacks remain separate
target-semantics gaps. These are proof coverage findings, not evidence that the
emitted C's lexical block is illegal. Resolve them before full FMI composition.

Sixteen added audit roots pass the unchanged axiom policy in
`build/fmi-error-embedding-audit.log`. The existing native lifecycle group
fails on the preceding FMU (`build/fmi-nominals-before.log`, OK instead of
Error), and the corrected FMU passes all thirteen groups and the actual-file,
source-link, mutation and publication-failure gate in
`build/fmi-nominals-artifact-gate.log`. The required full gate passed in
`build/fmi-nominals-full-gate.log` at `904e9bd`; its checked FMU has SHA-256
`1de662a5191c62573f146fc47781473d81400432b0a5a646ce1681bee4468e0f`.
[CI for 904e9bd](https://github.com/CogniPilot/rumoca_lean/actions/runs/34512618273)
also passed. This validates the guard correction while its full failed-call
proof obligations remain open.
No additional grammar case is admitted.

**Scope correction:** the instance declaration is now hoisted before the
empty-array branch, and both paths reuse one mode-guard constructor. The
existing validation/write suffix is unchanged. `SetterScope` proves the
hoisting law for arbitrary suffixes and caller continuations, preserving all
behaviors in `CCalls`, including wrong/divergent outcomes. It also proves the
actual emitted empty/null bodies terminate with unchanged memory in the typed
C machine and connects nonempty entry to the existing lifecycle predicate.
`BodyEmbedding.body_closed` now covers every generated signature without an
exclusion. The original `noDeclarations` restriction is retained; general C
block scopes have not been added. Nine new roots pass
`build/fmi-setter-scope-audit.log`. All thirteen existing native groups and the
actual-file/source-link/mutation gate pass in
`build/fmi-setter-scope-artifact-gate.log`. The existing argument/atomicity group
also checks null setter calls and empty-call state preservation. The required
full gate passed in `build/fmi-setter-scope-full-gate.log` at `1a53884`, and
[its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34516914151)
passed. The full-run FMU has SHA-256
`765662ef91d429089b4a22fd12dd29ec885f375a39a173c02bd4c8c35343a56f`.

**Public entry correction:** C array parameters previously failed before body
entry even for valid pointer arguments. The authored C machine now implements
the unsized-array adjustment in [C11 N1570 §6.7.6.3 paragraph 7](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf),
retaining explicit type resolution and rejection of unknown types, duplicate
names, arity mismatches and unsupported conversions. Generic proofs derive
coherent local value/type environments; complete ME continuous-state get/set
call theorems include entry, exact state observation/update, whole-heap results
and ordinary returns under arbitrary continuations. The existing body proofs
are reused with the same runtime function constructor as the renderer.
The FMI dictionary adds only the two required Float64 pointer spellings.
All twelve new roots and the full package audit pass in
`build/fmi-array-call-audit.log`. The FMI actual-file/source-build/mutation gate
and all thirteen existing native groups pass in `build/fmi-array-call-full-gate.log`.
The full run also passed its GALEC/eFMU archive, extracted-manifest and mutation
checks at `30ef448`; [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34521375057)
passed. These are selected function-tree call theorems with
explicit definition-table and storage premises, not an official-header parser,
actual adapter-byte or native ABI certificate. Remaining public signatures,
string binding, enabled callbacks and nonempty SetFloat64-loop execution remain
open; SR04 is not closed by this increment.

### SR05 — P2, unresolved: initialization rejects zero-duration/tolerance cases

[Runtime.body](../packages/backend-fmi3/RumocaFMI3/Runtime.lean) rejects enabled
`stopTime <= startTime` and `tolerance <= 0` for both interfaces. On the actual
binary, zero-duration and zero-tolerance initialization each return Error;
ordinary initialization returns OK. The existing initialization theorem
correctly proves this authored policy.

The reviewed initialization clause does not specify those exact strict
inequalities and permits CS to ignore tolerance. This is an unresolved
admission-policy question, **not a demonstrated unconditional requirement to
accept every such argument**. See
[FMI §2.3.2](https://fmi-standard.org/docs/3.0.2/#fmi3EnterInitializationMode).

**Close with:** justify each restriction from the numerical profile and
normative call contract, or relax it and update both reference and execution
proofs. Separate tolerance handling from stop-time validity. Review the entire
rejected-call behavior, including the resulting lifecycle state; do not infer
conformance just from `guard_reference`.

### SR06 — existing release gap: official checker and standalone layout differ

The unmodified [official eFMI Compliance Checker v1.0.1](https://github.com/modelica/efmi-compliancechecker/releases/tag/v1.0.1),
commit `edf33452ed0628bde1d8102c77b1030259ad5f57`, was rerun with its bundled
Lark 0.12.0 and colorama 0.4.6 plus the Nix Python/lxml environment. It returns
1 for the actual `.efmu` suffix, then 1 for a byte-identical `.fmu` alias because
it requires a top-level `eFMU/` directory. This repeats the
[documented discrepancy](efmi.md#official-checker-layout-discrepancy).

**New diagnostic evidence:** a disposable `.fmu` copy with each original member
prefixed by `eFMU/` returns **0**. Logs show checks of representation identities,
checksums, schemas, manifest references, GALEC parsing, variables and methods.
The copied member contents were unchanged. This only exercises deeper checker
paths: the transformed archive is not the certified standalone product, and
its pass does not resolve SR03 or establish production-C execution correctness.

Beta 1 Chapter 2 describes the selected standalone root layout; changing the
production archive merely to satisfy this checker's layout would need its own
normative review. E05/E06 stay open. Record an explicit resolution or accepted
tool limitation before a release claim.

### SR07 — existing release gaps: proof coverage and coding guidelines

The unit numerical theorem and eFMI source-to-archive theorem prove their
authored contracts. Neither establishes all prose obligations of FMI/eFMI.
For FMI, public CS time/status execution, failed calls/logging, lifetime,
correlated metadata and actual adapter/archive binding remain incomplete.
The typed tensor call result at this revision is not a tensor FMU theorem.
See [the exact contracts](../docs/verification.md) and
[FMI proof obligations](fmi3/contracts.md).

Beta 1 §5.2 also calls for coding-guideline compliance for generated C. The
repository has no complete MISRA AC AGC compliance/deviation argument. This is
missing release evidence, not a claim that a particular MISRA rule was proved
violated in this review. See
[Production Code Language in Beta 1](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
Functional preservation cannot replace that separate review. Native C
compilation, ABI/linkage and hardware remain outside the Lean theorem.

### SR08 — open correspondence gap: initialization across all three standards

MLS gives ordinary Real variables `fixed=false`; absent start attributes use
the applicable fallback rules. Zero is the fallback for the unit variable's
unmodified bounds. This does not itself add `x(0)=0` to the derivative equation.
See [MLS §4.9, Definition 4.7 and §4.9.1](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html).
Treating an unfixed start as fixed requires a diagnostic under
[MLS §8.6](https://specification.modelica.org/maint/3.7/equations.html).

The source theorem permits a supplied finite initial state, while FMI metadata
and GALEC Startup introduce their own initialization choices. Their common MLS
justification and diagnostic policy are not yet part of one reviewed contract.
This is an unresolved correspondence finding, not a demonstrated requirement
that all three interfaces expose the same initialization API.

**Close with:** specify the source initialization relation and allowed tool/host
choices, justify each from the clauses, then connect it to FMI initialization
and eFMI Startup with lowering and actual-artifact proofs. Any required source
diagnostic must point to the relevant declaration. Keep S01 and the stage gate
open until this is checked; no new grammar is needed to resolve the policy.

## Items checked without a new defect

The artifact contains both ME and CS descriptions of the same unit model,
using an internal shared kernel. The API capability flags do not advertise
FMI directional/adjoint derivatives merely because Solve AD proofs exist.
The integer-multiple CS communication profile is documented and rejected steps
preserve the instance in the existing native check. FMI headers are supplied
by the importing environment for source builds. eFMI identities, checksums,
GALEC declarations and the two representation manifests pass the available
independent checks described above. None of this closes the open proof items.

## Repair order and early-error discipline

1. **SR01–SR03:** repair source linkage/build metadata and eFMI status metadata,
   with their printer/semantic/actual-artifact contracts. Reuse existing
   package checks and integration entry points.
2. **SR04–SR05 and SR08/S01:** reconcile lifecycle and initialization against
   cited clauses across MLS, FMI and eFMI, then prove the affected successful
   and rejected behaviors.
3. Resume the existing small tensor/FMI work: typed public wrappers, instance
   storage/metadata, finite failure policy and source-to-archive composition.
   Arrays remain rejected in production until that complete path is checked.
4. Close SR06 and the SR07 release review obligations before claiming standards
   compliance or assurance comparable to an established verified compiler.

For each interface change, record **normative clause → independent predicate →
generated-body proof → actual-artifact observation** before implementing it.
Reviewers must challenge the predicate itself, especially if both the emitter
and reference table were written together. Use one focused external boundary
check where Lean does not model the tool or ABI; retain universal proofs for
the semantics. A passing schema validator or an extra collection of examples
does not close a missing contract.

The unchanged required gate remains
`nix develop .#verification --command lake test`; reuse cached package proofs
during local development. Review probes are not a substitute for that gate.
