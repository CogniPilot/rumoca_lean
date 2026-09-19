# Roadmap to a verified Modelica compiler core

Reviewed **2026-09-15**. **Grammar expansion is blocked.** The numerical
source-to-C core is formally checked; complete FMI/eFMI compiler verification
is unfinished. [Verification contract](../docs/verification.md) defines the
current guarantee. This file tracks the work needed to strengthen it.

Implementation owner: Codex. Independent proof and compliance reviewers are
not yet assigned. A proof count or percentage of checked boxes is not a
percentage of semantic coverage.

## Current position

**Tensor eFMU output admitted (merged):**

The XML serialization certificate now works by fragment cursor rather than a
whole-document decision, keeping kernel work linear; the tensor eFMU archive
certificate `Rumoca.CheckedTensorEFMIFiles.source_to_archive` completes in
about nine minutes at a peak near thirteen gigabytes, at parity with the
scalar archive certificate the gate already builds, and is gated. The CLI
admits tensor sources to eFMU output through the tensor archive certificate
under the reproducible identity mode, `tests/efmi-production.sh` publishes the
tensor fixture with certificate reuse, schema validation and a Production C
mutation control, and finding TF01 is closed. The required `nix develop
.#verification --command lake test` passed on 2026-09-18 in 81m28s with the
tensor archive certificate built cold (`build/tensor-fmi/full-gate-v37.log`).

**Kernel-efficient SHA-1 and the tensor manifest certificate (merged):**

The independent SHA-1 implementation now uses a structural schedule over
masked natural-number words, so the kernel reduces one hundred seventeen
compression blocks in fifteen seconds instead of exhausting memory, with the
digest and every certificate proposition unchanged; the fixed checker jobs
already run with the enlarged thread stack. The tensor eFMI manifest
directory certificate `Rumoca.CheckedTensorEFMIFiles.source_to_manifests`
now completes in about two and a half minutes within seven gigabytes and is
gated in the tensor C script; the tensor archive certificate is built but
still exceeds the budget because of the per-element XML serialization
certificate, so tensor eFMU output stays rejected while that step is being
restructured. The required `nix develop .#verification --command lake test`
passed on 2026-09-18 in 66m18s under load (`build/tensor-fmi/full-gate-v36.log`).

**Tensor eFMU archive theorem, Algorithm Code admission and production checker (merged):**

`tensor_archive_correct` assembles the tensor eFMU through the shared archive
generator and proves the member roster, checksums, container correlation and
stored ZIP bytes universally in the identity and model name; the fixed
`tensor-algorithm` certificate kind admits tensor sources to Algorithm Code
output through the CLI with certificate reuse and a mutation control, and the
tensor Production C actual-byte checker binds the read bytes per fragment.
The composed manifest and archive certificates were found to cost fifteen to
eighteen gigabytes with the per-element XML and per-byte SHA-1 machinery, so
tensor eFMU archive output stays rejected until the certificate machinery
scales; that work is in progress. The required `nix develop .#verification
--command lake test` passed on 2026-09-18 in 22m31s
(`build/tensor-fmi/full-gate-v35.log`).

**G01 constant-rate numerical C (certified kernel):**

`CConstant.contract_correct` emits the constant-rate IVP kernel universally in
the number of states: each rate is rendered as the exact base-ten content of
its literal and proved to round to nearest even, the Euler step is the finite
binary64 addition of the rate, and the counted sample executes each state's
independent trajectory. A fixed checker binds the actual bytes, a mutation of
a rate literal is rejected, and the native run gives `(7.5, -3)` after three
unit steps from zero. The required `nix develop .#verification --command lake
test` passed on 2026-09-18 in 69m16s under load
(`build/tensor-fmi/full-gate-v33.log`). The multi-state FMI adapter, its
certificate and admission follow in staged increments.

**Tensor reset conformance and tensor Production Code (merged batch):**

The native behavior matrix in `tests/fmi3.py` exercises 514 behavior cells
over all 75 functions of both FMUs and found that the tensor `fmi3Reset`
left an initialized instance unable to re-initialize; the tensor reset body
now restores the mode and every bookkeeping cell the scalar reset restores,
with `reset_mode_instantiated` and the `reinitializes` conjunct carried into
the adapter contract, and both matrices report no discrepancies. The tensor
eFMI path gained its Production Code with kernel refinement and the three
manifests with array dimensions, checksum and reference correlation, tied to
the compiler fixture and validated against the vendored schemas. The required
`nix develop .#verification --command lake test` passed on 2026-09-18 in
44m50s on this merge (`build/tensor-fmi/full-gate-v31.log`).

**G01 constant-rate development profile (derived proofs):**

A `constant_composition` production admits two or more scalar Real states
with one equation per state whose right-hand side is a signed decimal literal,
lexed as a value-erasing number token through the existing identifier
terminal so the LALR tables stay unchanged in kind; typed actions, AST and
located parse have soundness and completeness theorems. The source semantics,
resolution with duplicate and unbound-name rejection, and the Flat, DAE and
Solve lowering to a multi-state constant-rate IVP are proved, with exact
binary64 rounding of every literal and permutation invariance of the
equation order. `ConstantCompiler.prepare` has `prepare_correct` and the
compiler tests tie the `ConstantRates` fixture; production compilation still
rejects the profile. C emission, artifacts and admission are later increments.
See [constant rates](constant-rates.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-18 in 65m12s
on the merge of this profile with the no-heap call-graph policy for both
adapters and the tensor Algorithm Code (`build/tensor-fmi/full-gate-v30.log`).

**Array profile admitted to FMI 3 FMU output (production and stage record):**

`ParserActions.Parsed.located` lifts the total located-parse construction to
every action profile, so `compileTensor_complete` gives the existential
composition and the fixed checker emits
`∃ a, compileTensor input = .ok a ∧ TensorSourceBuildContract ...` like the
scalar theorem. The `rumoca` CLI dispatches array-profile sources to the
tensor artifact and the tensor FMU build gated by the `tensor-fmi3`
certificate; tensor eFMI and C output are rejected with a diagnostic, and the
driven profile stays rejected. `examples/TensorSquare.mo` is the admitted
example; `tests/fmi3.sh` publishes it through the CLI, requires certificate
reuse with no build, rejects an altered adapter byte and runs the FMU. The
recurring stage record for the enlarged subset is in the standards review with
findings TF01 to TF06 carried forward. Further grammar growth remains blocked
by K02 to K05. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-18 in 24m33s
(`build/tensor-fmi/full-gate-v29.log`).

**Tensor source-to-build certificate through the compiler (actual-artifact checks):**

`Rumoca.compileTensor` builds a tensor artifact from the array profile through
the proved lowering and carries the certified tensor kernel C, the rendered
adapter, the model description and the build description;
`tensorSourceBuild_correct` bundles the tensor IVP artifact contract, the
adapter contract, the build-description, identifier and XML contracts in the
shape of the scalar source-build contract, stated as an implication from a
successful compilation because the array profile has no total located-parse
constructor yet; reachability is exercised operationally by the development
`tensor-fmu` command. The fixed checker `verify_tensor_fmi3_build_files` reads
the same five actual files, kernel-checks the actual kernel and adapter bytes
against the rendered texts with the scalar certificate's byte machinery, and
emits `Rumoca.CheckedTensorFMI3Files.source_to_build` on the three permitted
axioms; it is registered as the cached `tensor-fmi3` certificate kind.
`tests/tensor-c.sh` builds the production-shaped tensor FMU, certifies its
extracted sources and runs it in FMPy with the proved values. The default CLI
still rejects the array and driven profiles; admission, the existential
composition and the enlarged-subset standards review remain the next
obligations. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-18 in 19m19s
with the tensor certificate built cold (`build/tensor-fmi/full-gate-v28.log`).

**Co-simulation step contract without interface assumptions (derived proofs):**

The tensor co-simulation numerical chain and accepted-step theorems are
generic over the C interface with the pinned type spellings and constants
bundled in one premise, and the contract instantiates the header-aware
floating-environment interface, so the round-to-nearest constant and the
`fmi3OK` return are now theorems rather than assumptions; the scalar path and
the unit FMU bytes are unchanged. The off-grid and over-bound `fmi3Discard`
behavior is proved for both logging outcomes by running the reused guard
prefix to the shared discard block and composing the scalar discard logging
over the tensor record, and it joins the null and lifecycle rejections in the
step contract and the adapter contract. The tensor contract's remaining
external premises are exactly the scalar path's: the modeled `fegetround` and
`floor` library returns, the kernel entry resolution facts and the finite
arithmetic premises. Nothing is emitted by production. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 12m15s
(`build/tensor-fmi/full-gate-v27.log`).

**Jacobian output after the co-simulation step (derived proofs and boundary run):**

The accepted tensor `fmi3DoStep` now calls the prepared Jacobian diagonal
entry once per step after the grid loop when the record carries the output;
the loop invariants preserve every instance member outside the state,
derivative and time regions, so the output region stays writable, and
`accepted_output_behaviors` adds to the step contract that the output region
reads the dense matrix with twice the input on the diagonal. The output-free
body and its theorems are unchanged. The native development FMU run reads
`J = (2, 0, 0, 4)` after the derivative evaluation in Model Exchange and after
three co-simulation steps, alongside the unchanged derivative and state
values. The remaining explicit items in the tensor contract are the off-grid
discard composition and the floating-environment interface premise. Nothing
is emitted by production. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 11m07s
(`build/tensor-fmi/full-gate-v26.log`).

**Jacobian output through the tensor derivative getter (derived proofs and boundary run):**

The tensor preamble declares the prepared `rumoca_square_jacobian_diag`
entry beside `rumoca_rhs`, with prototype and argument agreement proved and
bound by `TensorAdapter.Contract`. The tensor derivative getter is now
output-aware: when the record carries the output it calls the entry after the
derivative entry, and `deriv_output_behaviors` composes both kernel executions
under explicit resolution, definition and no-overflow premises, adding to the
contract that the output region reads the dense matrix with twice the input
on the diagonal and zeros elsewhere. The output-free case is unchanged. The
native development FMU run now reads `J = (2, 0, 0, 4)` after the derivative
evaluation in Model Exchange; the co-simulation step does not yet call the
entry, so `J` after `fmi3DoStep` still reads zero and that call with its
contract conjunct is the next obligation. Nothing is emitted by production.
See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 9m16s
(`build/tensor-fmi/full-gate-v25.log`).

**Jacobian diagonal as a prepared kernel entry (derived proofs and boundary check):**

The certified tensor kernel product now emits `rumoca_square_jacobian_diag`
as a second prepared entry beside `rumoca_rhs`; the tensor IVP artifact
contract and its fixed checker bind the actual `jacobian-diag.c` bytes with
the helper's call correctness, output reads and frame, and the native kernel
boundary asserts `diag(2u)` for a sample input. On the adapter side,
`TensorInstanceJacobian.jacobian_writes_events` executes the entry on an
instance through the observable machine with header premises taken from the
library, avoiding the adapter interface's pointer-type gap. The adapter does
not yet declare or call the entry, so the development FMU still reads `J` as
zero; the prototype declaration, the output-aware derivative getter, the
co-simulation step call and the contract conjuncts remain the next
obligation. Nothing is emitted by production. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 8m54s
(`build/tensor-fmi/full-gate-v24.log`).

**Square Jacobian diagonal helper (derived proofs):**

`CTensor.SquareDiagonal` adds the scratch-free C helper that zero-fills a
dense output tensor with the shared fill and writes `u[k] + u[k]` at each
diagonal cell with one strided counted loop over the symbolic volume, reusing
the existing diagonal memory model. Its call is proved to reach the dense
matrix with zeros off the diagonal and to preserve everything outside the
output, and each stored diagonal entry is a nearest finite value of the real
Jacobian entry of the square kernel established by the array-profile AD lemmas.
The helper is not yet emitted or called by the tensor adapter, so the native
run still reads `J` as zero; wiring it into the derivative getter and the
co-simulation step with the contract conjuncts is the next obligation. Nothing
is emitted by production. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 9m58s
(`build/tensor-fmi/full-gate-v23.log`).

**Kind-aware co-simulation exit and tensor instantiation token (derived proofs and boundary run):**

The tensor exit-initialization transition now branches on the instance kind
as the scalar body does, entering Event Mode for Model Exchange and Step Mode
for Co-Simulation; `TensorLifecycleHistory.lifecycle_cs_step` threads creation,
initialization and the Step Mode exit into an accepted `fmi3DoStep`. The shared
admission prefix and identity lemmas are generalized over the expected token
with the scalar token as default, so the scalar adapter is unchanged, and the
tensor factory validates the tensor metadata token, with the agreement between
the factory and the model description's `instantiationToken` a new conjunct of
`TensorAdapter.Contract`. The native development FMU run now passes in both
interfaces: derivatives `(1, 4)` and `x = (3, 12)` at `t = 3` in Model Exchange
and in three co-simulation steps. The Jacobian output is still not computed;
its wiring through a zero-fill and a strided diagonal write in the derivative
getter and the co-simulation step, with the dense-matrix theorem, is the next
obligation. Nothing is emitted by production. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 27m44s
with the FMI certificates rebuilt (`build/tensor-fmi/full-gate-v22b.log`); the
unit FMU's sources and model description are byte-identical to the previous
gate's.

**Initialization-entry contract lift and a native tensor FMU boundary run:**

The tensor `fmi3EnterInitializationMode` contract is now stated over the
emitted six-parameter function, so every conjunct of `TensorAdapter.Contract`
is literally about an emitted function. `tests/tensor-c.sh` assembles a
development FMU for the `TensorSquare` kernel from the retained adapter, the
certified tensor kernel C, the fixture model description and a build
description, compiles it cleanly, validates it with FMPy and drives it in Model
Exchange: with `u = (1, 2)` the derivatives read `(1, 4)` and three importer
Euler steps give `x = (3, 12)` at `t = 3`, matching the proved kernel. The run
is a boundary check outside the proof model and exposed three defects: the
tensor exit-initialization transition enters Event Mode for both kinds, so
co-simulation `fmi3DoStep` is rejected and needs the kind-aware Step Mode exit;
the factory validates the scalar witness instantiation token rather than the
tensor metadata token; and the Jacobian output is never computed, so `J` reads
zero. Fixing these three with proofs is the next obligation. The FMU is
retained under `build/tensor-fmi/`. Nothing is emitted by production. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 8m33s
(`build/tensor-fmi/full-gate-v21.log`).

**Header-conforming tensor adapter compiled as a standalone object (derived proofs and boundary check):**

Every tensor adapter function now carries exactly the pinned header prototype
for its name, proved position by position by `TensorFunctions.functions_signatures`;
the tensor record gained the event-time bookkeeping members the reused
completed-step body reads, initialized by both factories; and the state
setter's copy local is const-qualified. `tests/tensor-c.sh` now requires a
clean object compile of the retained adapter with the vendored FMI headers
under strict C11 flags with zero diagnostics, and it passes. The
initialization-entry lifecycle contract is still stated over the reduced
one-parameter function whose body the emitted six-parameter function shares;
lifting that statement to the header signature is the next obligation.
Nothing is emitted by production. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 9m11s
(`build/tensor-fmi/full-gate-v20.log`).

**Conforming array-member region pointers and a native adapter boundary check (derived proofs):**

The tensor bodies now stage every array-member region pointer as the address
of the first element, printed `&(m->x[0])`, which denotes the same instance
address at index zero, so every tensor theorem and contract keeps its
statement. The authored C body semantics gained array-to-pointer conversion
for subscripting an array member, backward compatible with pointer subscripts.
`tests/tensor-c.sh` now compiles the retained tensor adapter object-only with
the vendored FMI headers and strict C11 flags and fails on any incompatible
pointer type diagnostic; before the fix that compile reported twenty. That
compile also exposed two remaining development-stage defects for the next
increment: reused scalar event and discrete bodies reference record members
the tensor record lacks, and the reduced tensor lifecycle and query signatures
differ from the pinned header prototypes. Nothing is emitted by production.
See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 36m05s
with the C certificates rebuilt (`build/tensor-fmi/full-gate-v19.log`).

**Tensor helper set and full-list adapter render (derived proofs):**

The tensor preamble no longer carries the scalar model record or the scalar
helpers; it declares the prepared kernel entry `rumoca_rhs` with the prototype
the tensor bodies call, and the helper list is exactly the shared failure,
identity and reservation helpers. Call resolution is proved: every name the
tensor bodies call is a helper, an adapter function, a header function or the
declared kernel entry, and the entry's prototype matches the passed arguments.
The compiler check now renders the complete adapter for all seventy-five
pinned signatures of the `TensorSquare` kernel and retains it under
`build/tensor-fmi/adapter.c`. Review of that render found that array members
are addressed with the scalar `&(m->x)` idiom, a pointer to array where the
kernel prototype and copy locals take a pointer to `double`; correcting the
tensor bodies to the decayed array address and adding a native compile check
of the rendered adapter is the next obligation. Nothing is emitted by
production. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 10m29s
(`build/tensor-fmi/full-gate-v18.log`).

**Tensor adapter preamble and concrete rendered check (derived proofs):**

`FMI3.TensorStorage.declarations` renders the tensor instance record with
`double` regions of the symbolic volume for the state, input and derivative,
the flattened output region when present, and the slot, kind, mode, stop,
logging, environment and logger fields, plus the static pool of the deployment
capacity; the layout agrees with `TensorInstance` by proof and the text
tokenizes under the shared C grammar. `TensorFunctions.render` now uses this
preamble and `TensorAdapter.Contract` carries the layout and identifier
agreements. A compiler check renders the `TensorSquare` kernel's adapter to
concrete bytes, checks a representative function slice against the
function-section grammar and ties the actual prepared kernel to the fixture;
the bytes are retained under `build/tensor-fmi/adapter.c`. Review of that
render shows the helper section still carries the scalar model record and the
scalar `model_rhs`/`model_advance` helpers rather than the tensor derivative
entry with its buffer arguments; replacing the helper set is the next
obligation, together with the full-list concrete render. Nothing is emitted by
production. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 8m38s
(`build/tensor-fmi/full-gate-v17.log`).

**Tensor adapter function list, family contracts and adapter contract skeleton (derived proofs):**

`FMI3.TensorFunctions` maps every pinned header signature to its tensor body
or to the unchanged scalar family body, with the helper definitions and
literal pool facts, name distinctness and located rendering proved universally
in the shape and model name. `TensorFamilyContracts` re-plumbs the
model-agnostic absent-variable and capability-rejection execution cores over
the tensor list without duplicating their proofs. `TensorAdapter.Contract`
binds the rendered function text to public-API coverage, both family contracts
and every tensor behavioral contract in header order, and `render_contract`
proves it. The rendered preamble still reuses the scalar declarations, so the
tensor pool declaration is not yet bound; the co-simulation discard
composition and the floating-environment interface premise carry forward.
Nothing is emitted by production. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 9m01s
(`build/tensor-fmi/full-gate-v16.log`).

**Tensor co-simulation step execution and contract (derived proofs):**

`TensorDoStep.accepted_behaviors` proves the guarded tensor `fmi3DoStep` as
one observable-machine execution: the reused model-independent guard prefix,
the hoisted declarations, the outer grid loop with time advance, the
last-successful-time publication and the `fmi3OK` return, with the state
region equal to the finite Euler iteration, the time advanced by the step
count, the caller buffers written as the scalar body writes them and every
other instance preserved. Null and lifecycle rejections, printer denotation and
the tensor-native contract are proved, so all twenty-six behavioral functions
now have tensor bodies with contracts. Two items are explicit: the whole-call
`fmi3Discard` behavior still needs the scalar discard logging composition over
the tensor record, and the accepted case carries the round-to-nearest
floating-environment premise that the bare C interface cannot discharge, so
the tensor numerical lemmas must be rebased on the header-aware interface
before the contract is instantiable. Nothing is emitted by production. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 8m59s
(`build/tensor-fmi/full-gate-v15.log`).

**Tensor co-simulation time advance and guarded step body (derived proofs):**

`TensorDoStep` now advances the instance time cell by one inside each
declaration-free internal step, and `stepLoopT_reaches` carries the time base
through N steps alongside the state, derivative, input and other-instance
conclusions under explicit finite-addition premises. The complete guarded
tensor `fmi3DoStep` function is authored: the model-independent guard prefix of
the scalar body, the hoisted declarations, the outer grid loop and the return,
with its closed-block certification proved. The accepted-case execution of
that body and its bundled contract with the null, lifecycle and discard cases
remain open; the scalar step contract scaffolding is large and bound to the
scalar record. Nothing is emitted by production. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 8m51s
(`build/tensor-fmi/full-gate-v14.log`).

**Output-region writability and the N-step tensor co-simulation loop (derived proofs):**

The shared prepared tensor program contract `CTensor.Lowering.CallCorrect`
now also concludes that the emitted program's output region remains writable
from entry to the returned heap, proved from two memory lemmas (a whole-tensor
write leaves its cells writable and a store preserves every writable region)
and threaded additively through emission correctness, program calls, the typed
contract and every consumer without weakening any conclusion. With it,
`TensorDoStep.stepLoop_reaches` proves the outer grid loop of N internal steps
by induction: the state region reads the N-fold finite Euler iteration, the
derivative region reads the last result, inputs and every other instance are
preserved, and both regions stay writable. The per-step time advance, the
guarded `fmi3DoStep` body with its grid-policy discard and rejections, and its
bundled contract remain open. Nothing is emitted by production. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 29m29s
with the tensor and C certificates rebuilt (`build/tensor-fmi/full-gate-v13.log`).

**Declaration-free co-simulation step kernel (derived proofs):**

`TensorDoStep.derivative_run` restates the prepared derivative entry over any
well-formed instance heap from three region facts, `stepBody` is the
declaration-free per-internal-step body whose pointers, count and counters are
hoisted to the enclosing block, and `internalStepPure_reaches` runs one such
step as one observable-machine execution. Iterating the step is blocked by the
shared prepared-program contract, which exposes that the output region reads
the result and that outside cells are preserved but not that the output region
remains writable; strengthening that shared contract in the C package is the
next obligation, after which the guarded `fmi3DoStep` body, its grid-policy
discard, time advance and contract can be composed. Nothing is emitted by
production and no existing contract changed. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 9m29s
(`build/tensor-fmi/full-gate-v12.log`).

**Remaining tensor behavioral bodies and the co-simulation step kernel (derived proofs):**

Seven behavioral functions (version, debug logging, scheduled-execution
rejection, discrete evaluation and update, completed integrator step, event
indicators) are proved model-independent, so the tensor slice reuses the
scalar bodies and contracts verbatim over the tensor record. `TensorDoStep`
proves the tensor co-simulation kernel: one Euler iteration per state cell with
explicit finite-addition premises, the counted loop over the symbolic volume,
and one complete internal step that evaluates the derivative entry and
advances the state region as a single observable-machine execution. Twenty-five
of the twenty-six behavioral functions now have proved tensor bodies. The full
`fmi3DoStep` body with its grid-policy discard, null and lifecycle rejections,
time advance and multi-step iteration remains open because staging
declarations inside the solve loop conflict with the closed-block discipline.
Nothing is emitted by production and no existing contract changed. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-17 in 9m17s
(`build/tensor-fmi/full-gate-v11.log`).

**Tensor nominal-value getter (derived proofs):**

`FMI3.TensorNominals` proves the tensor `fmi3GetNominalsOfContinuousStates`
body: after the handle and lifecycle guard and the count and buffer checks, a
counted loop bounded by the symbolic volume writes the fixed nominal one into
every caller cell, preserving every other cell; the null handle is rejected.
With it, the tensor slice has authored bodies for eighteen of the twenty-six
behavioral functions. The remaining eight (version, debug logging, scheduled
execution rejection, discrete evaluation and update, completed integrator step,
event indicators, and the co-simulation step) and the tensor adapter renderer,
family contracts and adapter contract remain open. Nothing is emitted by
production and no existing contract changed. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 9m21s
(`build/tensor-fmi/full-gate-v10.log`).

**Tensor instance creation and a create-to-release history (derived proofs):**

`FMI3.TensorInstanceInit` and `TensorStaticFactory` prove the tensor
`fmi3InstantiateModelExchange`/`fmi3InstantiateCoSimulation` bodies: the shared
admission prefix and identity helper are reused unchanged, the bounded serial
reservation uses the existing atomic helper, and the reserved record is
initialized with slot, kind, time zero, Instantiated mode, callback capture and
the zero-fill loop over the state region. At the reservation scope of the
scalar factory theorem, a free slot yields an initialized owned handle with
every other slot and instance preserved, exhaustion returns null with no record
change, and a rejected identity returns null with the documented logging and
no reservation. `TensorLifecycleHistory.lifecycle_from_creation` threads
creation, initialization entry and exit, one derivative query and release from
an initial free pool back to the original owner map. The public-entry
composition through admission to creation in one theorem and the logged
rejection variant remain open. Nothing is emitted by production and no
existing contract changed. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 9m27s
(`build/tensor-fmi/full-gate-v9.log`).

**Tensor lifecycle modes, release and a composed history (derived proofs):**

`FMI3.TensorLifecycleModes` proves the tensor initialization entry and exit,
event and continuous-time entry and termination bodies over the static tensor
record: each writes only the instance's mode cell, rejects a null handle, and
rejects an illegal mode through the shared failure path, preserving every other
instance. `TensorFree` instantiates the model-agnostic release body for the
tensor pool, freeing exactly the owned slot and restoring the owner map.
`TensorLifecycleHistory.lifecycle_history` composes initialization entry and
exit, one derivative query and release from a created record, deriving the
observed statuses and the final owner map with explicit premises. The tensor
instance-creation body is not yet proved: the scalar admission prefix is
parameterized over the scalar model type, and the tensor record initializer
needs its own loop-based execution proof; the history therefore starts from the
created record as a premise. Nothing is emitted by production and no existing
contract changed. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 10m10s
(`build/tensor-fmi/full-gate-v8.log`).

**Tensor count queries, time setter and reset (derived proofs):**

`FMI3.TensorCountQueries`, `TensorSetTime` and `TensorReset` add the tensor
`fmi3GetNumberOfContinuousStates`, `fmi3GetNumberOfEventIndicators`,
`fmi3SetTime` and `fmi3Reset` bodies over the static tensor instance record.
The count query stores the symbolic volume as a `size_t` under an explicit
bound through a store lemma that keeps the cell type abstract, so the kernel
never evaluates the conversion range. The time setter validates finiteness and
writes only the instance's time cell; reset zero-fills the state region with a
counted loop bounded by the symbolic volume and the post-reset region reads the
kernel's initialization program. Each body has its sole terminating behavior,
null and non-finite rejections, other-instance preservation, denotation and a
consumable contract. Nothing is emitted by production and no existing contract
changed. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 10m07s
(`build/tensor-fmi/full-gate-v7.log`).

**Fused tensor derivative getter and machine transfer (derived proofs):**

`CCalls.Events.loop_call_reaches_events` and `loop_call_behaviors_events` in
the shared C package transfer a terminating typed-machine execution of a callee
to the observable call machine under an explicit `Resolves` agreement on its
nested helper call sites, without changing either machine. Through it,
`TensorContinuousStates.deriv_contract` proves the tensor
`fmi3GetContinuousStateDerivatives` body as one observable-machine run: the
sole terminating behavior calls the prepared derivative entry, delivers the
finite tensor derivative to the caller buffer with the instance's derivative
region holding the same values, preserves every other instance, and rejects a
null handle. The `Resolves` premise and finite execution remain explicit; the
tensor count queries were not completed because their successful-path proof
hit a kernel deep-recursion limit and remain open. Nothing is emitted by
production and no existing contract changed. See
[tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 9m45s
(`build/tensor-fmi/full-gate-v6.log`).

**Tensor continuous-state interface bodies (derived proofs):**

`FMI3.TensorContinuousStates` defines tensor `fmi3GetContinuousStates`,
`fmi3SetContinuousStates` and `fmi3GetContinuousStateDerivatives` bodies over
the static tensor instance record, reusing the counted copy core and the
finiteness validation loop. The state getter and setter have end-to-end
behaviors bound to instance `i`, preserving every other instance, with null and
count rejections, printer denotation and consumable contracts. The derivative
getter's copy suffix delivers the derivative region to the caller; its entry
call is proved separately in the typed machine, and the fused single-run
behavior awaits a typed-to-observable machine bridge, which remains open. The
unknown-reference failure path of the tensor Float64 accessors is now proved
through the memory machine. Nothing is emitted by production and no existing
contract changed. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 9m35s
(`build/tensor-fmi/full-gate-v5.log`).

**Tensor Float64 accessor bodies (derived proofs):**

`FMI3.TensorFloat64` defines tensor `fmi3GetFloat64`/`fmi3SetFloat64` bodies
over the static tensor instance record. One value reference denotes a whole
tensor variable; the getter dispatches time, input, state, derivative and the
optional output, the setter dispatches the writable input and state after
validating that every value is finite, and `nValues` must equal the referenced
element count. A shared counted copy loop with the symbolic volume as its bound
is proved once and reused. Each accepted reference has an end-to-end typed
machine behavior bound to instance `i`, preserving every other cell of every
other instance; the null-handle rejection is proved; the contracts carry the
printed text, closedness and printer denotation. Multi-reference aggregate
requests are rejected and remain the identified extension; the execution
witness for the unknown-reference failure path and the binding to an emitted
wrapper remain open. Nothing is emitted by production and no existing contract
changed. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 10m21s
(`build/tensor-fmi/full-gate-v4.log`).

**Tensor instance storage bound to the tensor right-hand side (derived proofs):**

`FMI3.TensorInstance` places a tensor model's time, state, input, derivative
and optional output tensors as contiguous `double` regions of one record in a
static instance pool, with no heap. Its roots prove readable inputs, a writable
derivative region, separation of distinct members and of distinct instances,
and preservation of every other instance when one is prepared, universally in
the shape and the pool index. `FMI3.TensorInstanceRhs` points the admitted
`TensorSquare` derivative entry at those regions, derives the entry predicates
from the instance heap and concludes, through `TensorModelRhs.behaviors`, that
the typed machine's sole behavior writes the finite tensor derivative into
that instance's derivative region and preserves every other cell of every
other instance. Finite execution, the environment facts and the count bound
remain explicit premises; the dense output binding, lifecycle, time base and
overflow policy remain open. Nothing is emitted by production and no existing
contract changed. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 9m00s
(`build/tensor-fmi/full-gate-v3.log`).

**Tensor FMI 3 model description (derived proofs and package checks):**

`Solve.TensorFMI3Model` pairs a model name with a prepared `PointwiseIVP`, and
`FMI3.TensorMetadata.modelDescription` builds its model description universally
over the tensor shape: one `Float64` per tensor variable with one `Dimension`
per extent, per-element `start` lists for the fixed-zero profile, the
derivative bound to its state, and a model structure whose entries record the
single input dependency. Audited roots prove renderer well-formedness under a
printable name, distinct value references, dimension products equal to the
tensor volume, start-list length, declared structure and dependency references,
and unchanged model-identifier decoding. A compiler check renders the
`TensorSquare` development kernel to the fixture bytes. Nothing is emitted by
production; the unit document, grammar, CLI and every mandatory contract are
unchanged. See [tensor arrays and AD](tensor-ad.md). The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 11m06s
(`build/tensor-fmi/full-gate-v2.log`).

**Tensor model right-hand-side contract (derived proofs):**

`FMI3.TensorModelRhs` restates the prepared tensor derivative entry as an
FMI-side function contract with the scalar contract's shape: printed text,
lexical denotation and typed-machine execution writing the finite tensor
derivative into its output buffer under any saved caller, with an exact frame.
Its three audited roots compose `PointwisePlan.correct`; no emitter, metadata,
lifecycle, mandatory contract or grammar changed. The required
`nix develop .#verification --command lake test` passed on 2026-09-16 in 10m06s
with all certificates reused (`build/tensor-fmi/full-gate-v1.log`). See
[tensor arrays and AD](tensor-ad.md#tensor-model-right-hand-side-contract).

**Cached artifact certificates (full gate passed):**

Actual-artifact certificates are now native Lake build products keyed by every
input byte, the source identity, the checker imports and the build
coordination, with retained input snapshots compared on reuse. eFMU generation
gains a reproducible identity mode under `SOURCE_DATE_EPOCH`, and the eFMI
gates stage their inputs at stable paths, so unchanged certificates are reused
across gates. Publication of an eFMU now consumes the checker's audit output
directly, and the axiom audit rejects a log whose final line lacks a newline.
The required `nix develop .#verification --command lake test` passed on
2026-09-16 in 36m16s with every certificate rebuilt cold; see
[verification performance](verification-performance.md). No grammar, semantics,
emission, solver, interface policy or proof obligation changed.

**Initialization from checked controls (full gate passed):**

The private interference frame now follows from current C destinations on the
same coupled history. Permissions distinguish caller objects outside the pool,
the executing invocation's borrowed record, and its own private reservation.
Invocation identity derives separation from every other private initializer,
including nested members and tensor offsets. Intermediate activity and private
reservation retention follow from the ledger and actual history.

Actual initializer controls establish their write destinations and exclude new
foreign calls. Atomic exchange and clear frames follow from their modeled
prototype conversions and one-cell updates. Actual public entry preserves all
current control permissions: the new internal call has no write or foreign
effect, and entering one resource cannot revoke another active borrow. Observing
a real return also preserves the remaining controls: only that original
invocation can return its borrow; successful publication cannot overwrite an
occupied resource; another call cannot publish a retained private reservation.

The source theorem retains the actual source/C/adapter/metadata/program and
earlier release, initialization and resource-history contracts. Its additional
controlled-initialization contract derives the private frame, initialized
record, returned handle and current publication from that same prefix. It does
not replace the existing general initialization contract or narrow production
source acceptance. Current foreign effects and importer-memory ownership remain
explicit; complete method control invariants and caller-buffer validity still
need to establish those permissions throughout every public lifecycle.

The owning-package checks passed at 03:38:56 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
04:26:45 UTC on 2026-09-16, with 1267 unchanged inputs and all
577 selected roots (29 new, 548 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft, dependency-isolation and semantic-review evidence is in
`build/c-private-retention/`: `completion-controls-v3.json`,
`controls-promotion-v3.json`, `controls-review-v3.md`,
`controls-extracted-v3.json`, `controls-extracted-fmi-v3.json` and
`controls-extracted-c-v2.json`. Integration, package, full-gate,
standards/upstream review and retained artifacts are under
`build/c-controlled-initialization/`.

Every FMU member is unchanged from `d304f4d`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Full public-control/lifecycle admission, importer and
callback effects, caller-buffer validity, native C11/static layout/ABI/fenv,
provenance, transitive allocation, MISRA and existing MLS/FMI/eFMI findings remain
open. K02–K05 still block grammar expansion and a complete assurance claim.

**Private reservation retention and initialization (full gate passed):**

A still-active original invocation now retains its private reservation through
the coupled history. Claims preserve occupied slots; release authority cannot
clear a private slot; another completion cannot publish it under the original
serial. The ledger derives intermediate descriptor retention even with thread
reuse. Starting from claimed-initializer control and the initial private entry,
the same framed history derives the final reservation, initialized record,
returned handle and current importer resource. These facts discharge this
factory completion's publication boundary. Its completion is outside the
prefix, so the proof does not assume the result it establishes. The source
theorem retains the actual C/adapter/metadata/program and preceding contracts.

The C write footprint now covers every supported internal transition, including
loop bodies, indirect call entry and saved return assignments. It resolves the
current destination without evaluating the RHS or enumerating tensor elements.
Actual execution preserves every other cell. Current resource authority then
derives separation from private initializer records, including nested members
and tensor offsets. Eventful and concurrent frames use the current shared heap;
foreign effects remain explicit. Complete method destination confinement and
caller-buffer separation are still needed to discharge the initialization
theorem's private interference premise for the whole public protocol.

The owning-package checks passed at 02:47:13 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
03:34:37 UTC on 2026-09-16, with 1260 unchanged inputs and all
548 selected roots (26 new, 522 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft, dependency-isolation and semantic-review evidence is in
`build/c-resource-histories/`: `source-retention-v2.json`,
`retention-promotion-v2.json`, `retention-review-v1.md`,
`retention-extracted-v1.json`, `retention-extracted-fmi-v1.json`,
`retention-c-reuse-v1.json`, `owned-write-frame-v1.json`,
`writes-extracted-v1.json`, `writes-c-reuse-v1.json` and `writes-review-v1.md`.
Integration, package, full-gate, standards/upstream review and retained
artifacts are under `build/c-private-retention/`.

Every FMU member is unchanged from `6f169ea`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Starting typed storage, complete admitted public
histories, destination/buffer/callback confinement, native C11/static
initialization/ABI/fenv correspondence, provenance, transitive allocation,
MISRA and existing MLS/FMI/eFMI findings remain open. K02–K05 still block grammar
expansion and a complete assurance claim.

**Resource origins and release histories (full gate passed):**

Resource updates now follow actual recorded C/host actions. The original ledger
computes fresh invocation identities, and each ordinary-use or release ticket
retains its exact public API and original instance argument. Ordinary completion
returns only its own resource. The actual captured clear consumes the release
resource; a history theorem proves that subsequent calls, thread reuse and slot
reuse cannot recreate the retired ticket. Its delayed void completion leaves
the current resource map, publication map and heap unchanged.

One coupled history projects to the same resource and computed publication
histories. Every later resource link and API origin follows from the initial
invariant. Starting with an empty host ledger, each usable handle has an actual
observed factory return with that slot and original serial. A successful factory
observation must still retain its private reservation; this boundary remains
explicit. The source theorem uses the same checked source, numerical C, adapter,
metadata and logged program, retaining its captured-release contract.

The owning-package checks passed at 01:57:44 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
02:44:19 UTC on 2026-09-16, with 1252 unchanged inputs and all
522 selected roots (57 new, 465 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft, dependency-isolation and semantic-review evidence is in
`build/c-instance-authority/`: `source-resources-v2.json`,
`resource-promotion-v2.json`, `resource-review-v2.md`,
`resource-extracted-v2.json`, `resource-extracted-fmi-v2.json` and
`resource-c-reuse-v2.json`. Integration, package, full-gate, standards/upstream
review and retained artifacts are under `build/c-resource-histories/`.

Every FMU member is unchanged from `d67ad60`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Complete public-call/lifecycle admission, private-value,
buffer/saved-destination and callback frames, private-reservation retention,
native C11/static initialization/ABI/fenv correspondence, provenance, transitive
allocation, MISRA and the existing MLS/FMI/eFMI findings remain open. Logical
resources are a verification design, not native generation tags. K02–K05 still
block grammar expansion and a complete assurance claim.

**Current handle authority and captured release (full gate passed):**

Logical handles retain the original observed factory serial and bounded slot;
the emitted C pointer is unchanged. Resource borrowing excludes overlapping
use of one instance and rejects stale generations, while other slots remain
independent. Actual successful initialization and factory completion issue the
resource for that initialized record; an unpublished reservation has no client
authority. Actual public release entry uses the invocation ledger's next serial.

Current releasing authority supplies the unchanged lease-checked release rule.
The actual atomic clear consumes that resource and reservation together, updates
computed publication, and leaves a heap-independent void-return suffix. A
reusable current-control footprint theorem preserves the original invocation
through host histories. Its release instantiation protects metadata only until
operand capture; later atomic/return states have an empty footprint. The actual
entry and history derive the pending clear arguments and saved continuation.

The source theorem binds this release contract to the actual numerical C,
adapter, metadata, literal preparation and logged runtime. Current resource
retention, flag representation and the prefix interference frame remain legal
caller obligations. The theorem does not infer authority from pointer bits or
claim arbitrary raw importer histories are valid.

The owning-package checks passed at 01:07:23 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
01:55:22 UTC on 2026-09-16, with 1238 unchanged inputs and all
465 selected roots (34 new, 431 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft, dependency-isolation and semantic-review evidence is in
`build/c-publication-history/`: `source-authority-v1.json`,
`authority-promotion-v2.json`, `authority-review-v2.md`,
`authority-extracted-v2.json`, `authority-extracted-fmi-v2.json` and
`authority-c-reuse-v2.json`. Integration, package, full-gate, standards review
and retained artifacts are under `build/c-instance-authority/`.

Every FMU member is unchanged from `380cb59`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Complete caller/resource histories, private-value and
buffer/callback frames, native C11/static initialization/ABI/fenv correspondence,
provenance, transitive allocation, MISRA and remaining MLS/FMI/eFMI findings
stay open. K02–K05 still block grammar growth and a complete assurance claim.

**Computed publication and release completion (full gate passed):**

Publication now extends the same actual reservation history with computed
private/published phases. Claims, clears, observed returns, bounded addresses
and original invocation serials determine the transitions. Its projection
preserves the exact physical leases and flag representation. Every current
publication has an actual matching factory-completion event. Forward transition
proofs also show that matching completion really publishes.

The source theorem retains the actual C/adapter/metadata and prepared-runtime
contracts. The initialization bridge proves that the same actual completion
returns the initialized record and publishes its retained reservation. Typed
initial storage, private-record interference and retention remain explicit
premises for the complete legal lifetime protocol to establish. Observation
does not establish a caller's authority to use or release the handle.

A further source theorem starts from the authored static declaration
initialization and derives writable storage at every reached reservation.
Callbacks and host memory actions must preserve object descriptors; numerical
values remain mutable. The original heap must provide fresh static blocks.
No reached writable-pool premise or successful initializer run is supplied.
A combined source theorem connects static storage, the exact physical and
publication histories, and successful initialization under one program and
invocation ledger. Native static initialization remains a separate
correspondence obligation.

After the emitted release's real atomic clear, its remaining instructions are
enabled, silent, preserve the entire current heap and decrease an own-step
count. The generic suffix remains valid under admitted interference without
a metadata frame. Its original invocation returns void even if another factory
has reused the storage. That delayed completion cannot alter publication of a
new lease. Existing lease-checked release rules are unchanged.

The owning-package checks passed at 00:17:00 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
01:05:09 UTC on 2026-09-16, with 1230 unchanged inputs and all
431 selected roots (49 new, 382 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft and dependency-isolation evidence is in `build/c-private-initialization/`:
`initialized-publication-v3.json`, `release-tail-v2.json`,
`source-static-initialization-v1.json`, `source-creation-histories-v1.json`, `publication-promotion-v3.json`,
`publication-review-v3.md`, `publication-c-reuse-v2.json` and
`publication-extracted-fmi-v2.json`, `publication-extracted-all-v3.json` and
`publication-dependency-reuse-v3.json`. Integration, package, full-gate,
standards/upstream review and retained artifact records are under
`build/c-publication-history/`.

Every FMU member is unchanged from `93192e8`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. The complete legal host/callback/buffer protocol,
current lifetime authority, native C11/static initialization/ABI, fenv,
provenance, transitive allocation, MISRA and remaining MLS/FMI/eFMI findings
stay open. K02–K05 still block grammar expansion and a complete assurance claim.

**Concurrent initialization through host observation (full gate passed):**

The source-bound theorem now connects the checked source, numerical C,
prepared runtime and actual public history to successful reservation,
initialization and host-observed return. The raw history derives the original
factory arguments and saved caller. Its actual exchange supplies the index,
observation, event, new heap and successful continuation. The real helper
return, capacity guard and instance selection derive initializer entry.

The initializer runs its emitted metadata, prepared Solve state, clock,
lifecycle and callback stores. A reference execution stays related to the
current heap only on its private record. Its actual internal steps are enabled,
silent, preserve the exterior and reduce a control-derived remaining-step
count. Zero means actual root halting. The returned handle, initialized values,
writable storage and slot metadata are proved at host-observed completion.
Scheduler fairness is not asserted.

Shared-history invariants use the current heap and original invocation serial.
Thread reuse cannot reuse that identity. A distinct initializer's actual C
steps preserve every member of this record, without enumerating array elements.
The complete successful factory continuation derives its exterior frame,
including helper return, guard and selection; the successful scan preserves
the whole shared heap.

Typed pool storage at the reached exchange and private-record interference
remain explicit premises. The complete legal host/callback/buffer protocol must
establish them and connect actual completion to live-handle authority and
authorized release. The physical reservation registry remains a separate
proved component; pointer bits or a busy flag do not establish caller authority.
The source theorem does not yet combine these into one complete lifetime rule.

The owning-package checks passed at 23:23:46 UTC on 2026-09-15.
The required `nix develop .#verification --command lake test` passed at
00:13:37 UTC on 2026-09-16, with 1217 unchanged inputs and all
382 selected roots (33 new, 349 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft and dependency-isolation evidence is in `build/c-reservation-registry/`:
`source-initialization-v3.json`, `initialization-promotion-v2.json`,
`initialization-review-v2.md` and
`initialization-extracted-c-v1.json` plus
`initialization-extracted-{fmi,all}-v2.json`. Integration, package, full-gate,
standards/upstream review and retained artifact records are under
`build/c-private-initialization/`.

Every FMU member is unchanged from `88b8f7c`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Native static initialization/C11/ABI, callback/fenv
correspondence, provenance, transitive allocation, MISRA and remaining
MLS/FMI/eFMI findings stay open. K02–K05 continue to block grammar growth and
a complete assurance claim.

**Computed reservation histories through actual claims (full gate passed):**

The source-bound theorem now derives current reservation/flag representation
from the typed C pool's initially free flags and the raw public host history.
Actual selected controls, operands and recorded invocations compute each
registry update. Successful exchanges record the enclosing factory's serial;
busy exchanges retain the previous reservation. Actual false stores clear only
the addressed slot, leaving this pool unchanged when the address is outside it.
No next-map, owner, observation or per-step atomic annotation is supplied.

Invocation replay proves that recordings of the same raw actions have the same
ledger. The same derived registry therefore supplies actual factory claims,
original arguments, bounded indices and saved continuations. Successful claims
exclude any later reservation by that invocation, including after helper return
and across thread reuse. Event tags need not be injective.

The actual generated program proves clear-call operands and ordinary flag
frames. Importer memory and logger effects must preserve atomic cells; these
are explicit foreign-boundary contracts. Original factory inputs must satisfy
the represented ABI profile. Neither valid identity strings nor supported CS
requests are required; rejection paths remain covered.

Additional C proofs use mathlib's `Set.EqOn` to transport actual typed stores
and assignments across interference outside their symbolic address region.
They preserve values, not merely cell types and permissions, and retain the
other heap's exterior. Conservative operand certificates cover the body and
loop evaluators. Every actual initializer store, including slot metadata and
nested Solve state, satisfies the selected-record footprint. These lemmas
supply the memory component; complete concurrent initialization remains open.
The combined checked draft is `build/c-factory-history/initialization-footprint-v1.json`.

This is a physical reservation registry. It records a clear even when the
caller lacks release authority. The existing lease-checked release semantics
are unchanged. Private initialization, actual handle publication, legal later
metadata/buffer and release authority, and stale/reused handle safety remain
open. A reservation or pointer alone is not published live-instance authority.

The owning-package checks passed at 22:33:31 UTC on 2026-09-15.
The required `nix develop .#verification --command lake test` passed at
23:21:32 UTC on 2026-09-15, with 1204 unchanged inputs and all
349 selected roots (39 new, 310 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft and dependency-isolation evidence is in `build/c-factory-history/`:
`source-registry-v4.json`, `initialization-footprint-v1.json`,
`registry-promotion-v2.json`, `registry-review-v2.md` and
`registry-extracted-{c,fmi,all}-v2.json`. Integration, package, full-gate,
standards/upstream review and retained artifact records are under
`build/c-reservation-registry/`.

Every FMU member is unchanged from `af477e9`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. The initial flags belong to the authored typed C
semantics; native static initialization/C11/ABI, callback/fenv correspondence,
provenance, transitive allocation, MISRA and remaining MLS/FMI/eFMI findings stay
open. K02–K05 continue to block grammar growth and a complete assurance claim.

**Public factory histories through slot claims (full gate passed):**

The source-bound claim theorem now starts with the raw public host history.
It derives the original ME/CS factory arguments, the exact saved reservation
continuation, the prepared flag-array pointer and the bounded exchange index.
It no longer requires a separately supplied helper-entry interval. That same
actual C step supplies its event, observation, recorded invocation and slot
ownership transition. A successful helper continuation remains silent and
returns the selected index. The same factory invocation cannot reserve again
anywhere in its remaining host history, including after the helper returns.
Later calls on a reused thread receive new invocation identities.

The factory control proof covers supported and rejected CS requests, both
identity outcomes, optional rejection logging, reservation, and the closed
post-scan suffix. An unconditional return makes rejected creation code
unreachable. Generic context lemmas preserve the literal saved caller and
exclude premature local halting. Host histories include other invocations,
completions and admitted heap changes, as well as C execution.

The original factory call must satisfy the represented ABI argument profile
(`AdmitsFactories`). It need not contain valid identity strings or request
supported CS capabilities. Current owner/flag representation remains an
explicit heap premise. Ownership at the successful atomic result does not
establish its preservation under arbitrary later changes. Concurrent private
initialization, actual live-handle publication and subsequent legal lifetime,
metadata/buffer and release authority remain open.

The owning-package checks passed at 21:40:48 UTC on 2026-09-15.
The required `nix develop .#verification --command lake test` passed at
22:31:16 UTC on 2026-09-15, with 1192 unchanged inputs and all
310 selected roots (30 new, 280 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft and dependency-isolation evidence is in `build/c-scan-context/`:
`factory-history-promotion-v3.json`, `factory-history-review-v2.md`,
`fmi3-factory-once-v1.json` and `factory-extracted-{c,fmi,all}-v3.json`.
Integration, package, full-gate, standards/upstream review and retained artifact
records are under `build/c-factory-history/`.

Every FMU member is unchanged from `eb412f9`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Native C11/ABI, callback/fenv correspondence, provenance,
transitive allocation, MISRA and remaining MLS/FMI/eFMI findings stay open.
K02–K05 continue to block grammar growth and a complete assurance claim.

**Slot claims and suspended callers (full gate passed):**

Actual reservation uses the computed enclosing factory invocation serial as
its slot lease and as the origin of the same recorded C step. Starting at the
real helper entry, its atomic operation supplies the bounded slot, observation
and ownership transition. On success, subsequent helper steps are silent,
schedule no further calls and return that index under finite interleavings.
The actual factory suffix cannot reserve again after the helper returns,
including its exhaustion branch. Source theorems retain the same actual pool,
header, table, numerical C, adapter and metadata contracts.

Generic continuation proofs give exact C step correspondence in both directions
beneath a suspended caller, preserving events and heap. The root-return boundary
is explicit. Actual shared-history invariants retain the literal caller and
derive each reached nested call's context. A source-bound helper-domain theorem
uses this to exclude reservation inside identity validation without requiring
the suspended factory's reservation suffix to satisfy that helper policy.

The complete factory prefix must still derive helper-entry/return intervals
from its raw host history. Current flag/owner representation, concurrent private
initialization, live-handle publication and later legal lease/interference
histories remain open. Control preservation does not assert ownership survives
arbitrary future heap changes. No progress/fairness or native C11 claim is added.

The owning-package checks passed at 20:49:47 UTC on 2026-09-15.
The required `nix develop .#verification --command lake test` passed at
21:38:47 UTC on 2026-09-15, with 1179 unchanged inputs and all
280 selected roots (36 new, 244 retained). No unexpected axioms, changed-module
warnings or source drift were found. The three existing audits retain every
previous root; no unit test suite was added. Root counts do not measure semantic
coverage.

Draft review and dependency-isolation evidence remains in
`build/c-host-boundary/`: `scan-claim-promotion-v2.json`,
`context-promotion-v1.json`, `scan-claim-review-v2.md`, `context-review-v1.md`
and `claims-context-extracted-v1.json`. Integration, package, full-gate,
standards/upstream review and retained artifact records are under
`build/c-scan-context/`.

Every FMU member is unchanged from `57d361c`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public interface emission are
unchanged. Existing artifact, native and mutation checks pass. Only these three
evidence documents change after the frozen gate.

Factory identity-resumption follow-ups remain drafts outside this checkpoint.
Native ABI/C11, callback/fenv correspondence, provenance, transitive allocation,
MISRA and remaining MLS/FMI/eFMI findings stay open. K02–K05 block grammar growth.

**Host histories and reservation origins (full gate passed):**

The host boundary executes the existing C scheduler, admits calls through the
actual public table, observes their halted results and permits repeated calls.
Host memory changes have an explicit policy relation. Computed invocation
records retain the original thread, function and arguments; issued serials
form a strictly increasing interval and are not recycled at completion.

Existing typed C executions embed with exact events, values and output heaps.
The source-bound initial factory/release contract assigns the factory's
invocation serial as its lease and passes its actual returned pointer to release.
Release gets a new invocation serial while using the original factory lease.
These complete calls have matching intermediate states for sequential
composition; they do not establish arbitrary concurrent lifecycle histories.

The actual generated bodies prove a closed non-factory call domain. Generic C
step equivalence and control invariants tied to each recorded invocation derive
the enclosing ME/CS factory for every reached reservation helper or exchange.
The raw host history supplies the descriptor, fresh serial and prior invocation
witness; no later factory or owner annotation is assumed. Successful claim
handoff, concurrent initialization, live-handle publication and later legal
ownership/frame histories remain open.

This checkpoint also includes the release-origin and ordinary flag-frame
proofs described below. The combined package checks passed at
19:55:20 UTC on 2026-09-15. The required
`nix develop .#verification --command lake test` passed at 20:46:20 UTC
on 2026-09-15, with 1166 unchanged inputs and all 244 selected roots
(78 new, 166 retained). No unexpected axioms, changed-module warnings or source
drift were found. The three existing audits retain every earlier root; no
unit test suite was added. A root count is not a measure of semantic coverage.

Evidence is in `build/c-host-boundary/`: `integration-v1.json`, `package-v1.*`,
`full-gate-v1.*`, `standards-review-v1.json`, `upstream-review-v1.json` and
`artifacts-v1.*`. The earlier release/frame evidence remains in
`build/c-release-frames/`. The combined gate covers its pre-publication EOF
cleanup as well as all new host/recording/origin modules.

Every FMU member is unchanged from `4b55612`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public interface emission are
unchanged. Existing artifact, native and mutation checks pass. Only these
three evidence documents change after the frozen gate.

Further scan-claim work remains an ignored draft under `build/`; it is not
part of this checkpoint. Complete legal histories, native C11/ABI and
callback/fenv correspondence, provenance, transitive allocation, MISRA and the
remaining MLS/FMI/eFMI findings remain open. K02–K05 block grammar expansion.

**Release origins and ordinary flag frames (full gate passed):**

Generic C proofs classify real shared steps as ordinary frame-preserving work
or exceptional foreign calls. Prepared string and math bindings retain atomic
flag values. Under an explicit logger flag-preservation contract, only atomic
operations may change them. Without that contract, a flag-changing step is
attributed to an actual atomic or canonical importer logger call. Source binding
supplies the actual adapter table, types and library; no per-step ordinary
annotation is assumed.

Atomic exchange/store preserve successfully loaded ordinary cells. Their cell
types prove non-aliasing without an extra address-inequality premise. A generic
heap-dependent invocation rule separates own execution from other-thread
interference. Actual public release preserves its slot metadata through entry,
parameters, local initialization, the null guard, store and void return. Null
release requires no metadata cell.

The source release theorem supplies the actual function, header and 32-slot
pool. Valid original metadata and an explicit other-thread metadata frame
determine its release address. A represented current lease supplies the enabled
unique atomic step, ownership update, exact event and return continuation.
Successful release, converted arguments and next-state annotations are not
premises. Complete legal histories must still derive interference and current
lease conditions; original metadata alone does not authorize a stale or
duplicate release.

The affected package checks passed at 18:59:11 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 19:48:41 UTC
on 2026-09-15, with 1151 unchanged inputs and all 191 selected roots
(25 new, 166 retained). No unexpected axioms, changed-module warnings or source
drift were found. The three existing audits retain all previous roots; no test
suite was added. Evidence is in `build/c-release-frames/`:
`integration-v1.json`, `package-v1.*`, `full-gate-v1.*`,
`standards-review-v1.json`, `upstream-review-v1.json` and `artifacts-v1.*`.

Every FMU member is unchanged from `4b55612`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public interface emission are
unchanged. Existing artifact, native and mutation checks pass. Three evidence documents were updated after that frozen gate. A later
pre-publication EOF cleanup is included in the combined gate above.

The host-boundary and recorded reservation-origin follow-ups are integrated
in the combined checkpoint above. Complete legal histories and live-lease
handoff, native C11/ABI/fenv/callback correspondence, provenance, transitive
allocation, MISRA and remaining MLS/FMI/eFMI findings stay open. K02–K05
continue to block grammar expansion.

**Reservation bounds and actual atomic operations (full gate passed):**

The shared C invocation invariant covers actual helper entry, parameter binding,
local initialization and every scan-loop prefix under shared-heap interleavings.
It retains the original flag pointer and bounded index until the original caller
resumes. The source theorem derives the actual helper, header types and emitted
32-slot pool from the same source/adapter contract. The validated factory suffix
obtains its helper arguments from fresh locals and concrete globals.

Represented current flags supply an enabled, unique actual reservation step and
its lease annotation, with the busy result, exact event, ownership update and
other-thread control frame. Neither successful reservation nor argument
conversion or a next-state annotation is a premise. Complete public factory
entry, release authorization, fresh lease assignment and ordinary/logger flag
frames remain open. An unsuccessful concurrent scan does not prove that all
slots were busy at one instant.

The separate generated-call proof derives Boolean conversion and actual atomic
memory effects after finite shared executions from public entries. It retains
exact events and return continuations without extra conversion or value-policy
premises. Its unrestricted atomic pointers do not establish release authority.

The affected package checks passed at 18:09:27 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 18:57:47 UTC
on 2026-09-15, with 1142 unchanged inputs and all 166 selected roots
(27 new, 139 retained). No unexpected axioms, changed-module warnings or source
drift were found. The existing three audits retain all previous roots; no test
suite was added. Evidence is in `build/c-reservation-bounds/`:
`integration-v1.json`, `package-v1.*`, `full-gate-v1.*`,
`standards-review-v1.json` and `artifacts-v1.*`.

Every FMU member is unchanged from `00a235c`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public interface emission are
unchanged. Existing artifact, native and mutation checks pass. Only these
three evidence documents change after the frozen gate.

The ordinary flag-frame and callback-attribution follow-up remains a checked
draft under `build/`, separate from this checkpoint. Native C11/ABI, full legal
histories, provenance, transitive no-allocation, MISRA and remaining MLS/FMI/eFMI
findings stay open. K02–K05 continue to block grammar expansion.

**Concurrent slot histories and atomic-call values (full gate passed):**

Reusable C proofs characterize actual shared-heap scheduler steps and preserve
operand restrictions through calls, returns and finite interleavings. The direct
Boolean checker is equivalent to the structural predicate. FMI derives
reservation=true and release=false from the generated trees and actual argument
evaluation. Its linked address map excludes indirect atomic aliases. The source
theorem supplies this invariant from the actual adapter/header contract and
ordinary public invocations, without later-call annotations or an extra atomic
argument policy.

The separate ownership simulation derives atomic steps from represented flag
memory and connects annotated C histories to independent lease transitions.
An owned slot cannot be successfully reclaimed without its prior lease being
released. Source binding supplies the generated table, library bindings and
emitted 32-slot pool. Complete factory-path classification still needs valid
flag-address origins, release authorization and atomic-value frames for other
effects; these obligations are not assumed away by the call-value proof.

The affected package checks passed at 17:16:36 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 18:07:31 UTC
on 2026-09-15, with 1133 unchanged inputs and all 139 selected roots
(45 new, 94 retained). No unexpected axioms, changed-module warnings or source
drift were found. No test suite was added. Evidence is in
`build/c-concurrent-slots/`: `integration-v1.json`, `package-v1.*`,
`full-gate-v1.*`, `standards-review-v1.json`, `upstream-review-v1.json`
and `artifacts-v1.*`.

Every FMU member is unchanged from `fdb6bc8`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

The atomic-operation, reservation-bound and flag-frame follow-ups are checked
drafts under `build/`; they are not integrated at this checkpoint. Native atomics/ABI, full legal histories,
provenance, transitive no-allocation, MISRA and remaining MLS/FMI/eFMI findings
stay open. K02–K05 still block grammar expansion.

**Runtime storage and state-setter permissions (full gate passed):**

Generic C proofs lift store-stable heap relations through foreign calls and
modeled thread interleavings. The selected string, atomic and math bindings
preserve object existence, types and permissions. The source-bound prepared
runtime combines this with the call-depth bound under an explicit logger storage
contract. Without that contract, any observed storage change is attributed to
an actual logger execution, with its arguments and trace position. These are
modeled storage properties; native/transient allocation and race freedom remain
separate obligations.

The state-setter policy identifies continuous states through the actual XML's
ModelStructure derivative links. Initialization and reinitialization attributes
determine the phase permissions. Lean proves exact correspondence with the
existing guard for every accepted XML witness and connects it to the actual
source/setter contract. The ME interpretation follows accepted FMI clarification
#1956; the Table 17 editorial conflict remains explicit in the standards review.

The affected package checks passed at 16:16:22 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 17:12:17 UTC
on 2026-09-15, with 1125 unchanged inputs and all 94 selected roots
(32 new, 62 retained). No unexpected axioms, changed-module warnings or source
drift were found. The existing separate audits retain every prior root; no
test suite was added. Evidence is in `build/c-runtime-resources/`:
`integration-v1.json`, `package-v1.*`, `full-gate-v1.*`,
`standards-review-v1.json` and `artifacts-v1.*`.

Every FMU member is unchanged from `026bc92`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public-call emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

The annotated concurrent lease-history and atomic-call-value follow-up proofs
are checked drafts under `build/`; they are not integrated at this checkpoint. Complete factory-path
classification, native/ABI, full legal histories, provenance, transitive
no-allocation and MISRA obligations remain open. K02–K05 and the remaining
MLS/FMI/eFMI findings still block grammar expansion.

**Source-bound runtime and call depth (full gate passed):**

One prepared environment contains the actual generated function table,
string/atomic/math bindings and an arbitrary logger effect. Generic linking
preserves existing bindings and registers function addresses only for imported
entries. The C rank invariant survives every internal step, return and returning
foreign choice. Every finite execution prefix in this FMI environment has at
most three modeled continuation frames, without assuming successful termination.
The source theorem derives the literal pool, public printer coverage and
concrete object/fenv interface from the actual adapter contract. It uses the
emitted 32-slot configuration, with no separate type, pointer-policy or rank
premise. Native layout, library/callback internals, native stack bytes and
transitive allocation remain outside this bound.

The affected package checks passed at 15:17:26 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 16:14:54 UTC
on 2026-09-15, with 1119 unchanged inputs and all 62 selected roots
(29 new). No unexpected axioms, changed-module warnings or source drift were
found. The existing separate package audits retain every prior root. Evidence
is in `build/c-call-depth/`: `integration-v1.json`, `package-v1.*`,
`full-gate-v1.*`, `upstream-review-v2.json` and `artifacts-v1.*`.

Every FMU member is unchanged from `f0694e8`. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public-call emission are unchanged.
The existing artifact, native and mutation checks pass; no test suite was added.
Only these three evidence documents change after the frozen gate.

This accepts the modeled execution-depth and source linkage increment.
The storage and state-setter follow-up proofs remain checked drafts under
`build/`; they are not accepted package/artifact results at this checkpoint.
Native resource, ABI, complete legal-history, provenance and MISRA obligations
remain open. K02–K05 and the whole-subset standards findings still block grammar
expansion; no full standards or CompCert-level whole-compiler claim follows.

**Generated call policy (full gate passed):**

The shared C package has a complete structural call inventory and an independent
admission predicate. Its executable checker walks the tree directly; Lean
proves exact Boolean equivalence to checking the full inventory for every
predicate and function. FMI classifies generated helpers, library routines and
importer callbacks. Checked ranks exclude cycles in the complete prepared
direct-call graph, including numerical definitions. The shared resolver connects
named calls to that graph, and numerical-kernel execution is proved unable to
issue a scheduler call. The source consequence derives the policy from the
mandatory actual adapter/header contract without an extra rank assumption.

The affected package checks passed at 14:22:06 UTC on 2026-09-15. The required
`nix develop .#verification --command lake test` passed at 15:09:42 UTC
on 2026-09-15, with 1114 unchanged inputs and all 33 selected roots.
No unexpected axioms, changed-module warnings or source drift were found.
The policy audits have separate modules in the existing package check libraries;
unrelated audits retain Lake's normal cache. Evidence is in
`build/c-call-policy/`: `integration-v3.json`, `package-v3.*`,
`full-gate-v1.*`, `upstream-review-v2.json` and `artifacts-v1.*`.

Every FMU member, including its native library, is unchanged from `d757659`.
The eFMU changes only generation identities and dependent references/checksums
in three manifests. Numerical C, GALEC, Production C, grammars, solver policy,
metadata and lifecycle emission are unchanged. The existing artifact, native
and mutation checks pass; no test suite was added. Only these three evidence
documents change after the frozen gate.

This accepts call classification and direct-call graph ranking. Complete
execution/continuation composition, native/transitive no-allocation, callback
reentry, layout, concurrency and MISRA remain open. K02–K05 still block grammar
expansion; this is not a full standards or CompCert-level whole-compiler claim.

**SR09 empty-setter correction and public-export coverage (full gate passed):**

Empty Float64 and absent-type setters now use the general setter endpoint
rule. Terminated instances reject them; CS Step Mode retains empty calls.
The nonempty Float64 validation domain is unchanged. Complete success and
lifecycle/count rejection contracts preserve every modeled callback outcome,
prepared diagnostics, raw arguments and source/history composition.

Every emitted header signature now has mandatory coverage by a named public
execution/printer contract. The fixed actual-file checker supplies this witness
for the same adapter table and literal pool. The general C return-continuation
law proves unused caller suffixes cannot change the modeled call behavior;
it does not weaken the C machine or the previous behavior contracts.

The combined core/C/FMI/compiler checks passed at 13:01:38 UTC. The required
`nix develop .#verification --command lake test` passed at 13:52:47 UTC on
2026-09-15 with 1107 unchanged inputs and all 436 selected roots. There were
no unexpected axioms, changed-module warnings or input drift. Evidence is in
`build/c-factory/setter-endpoints/`: `package-v3.*`, `full-gate-v1.*`,
`integration-v3.json`, `standards-review-v1.json`, `upstream-review-v1.json`
and `artifacts-v1.*`.

The actual FMU changes exactly 13 setter guard lines and its native library;
every other member is byte-identical to `4db587a`'s retained FMU. The eFMU
changes only generation identities and dependent references/checksums in three
manifests. Numerical C, GALEC, Production C and metadata behavior are unchanged.
The existing native boundary check now includes terminated empty setters for
both interfaces; no test suite or grammar was added. Only these three evidence
documents change after the frozen gate.

This accepts the empty-setter repair and complete raw-call contracts. The
separate nonempty local-state setter wording review, complete legal-history
correspondence, native/ABI, provenance, concurrency, no-heap and MISRA obligations
remain open. K02–K05 still block grammar expansion; this is not a full FMI/eFMI
conformance or CompCert-level whole-compiler claim.

**Unsupported public FMI calls (full gate passed):**

The mandatory adapter proposition includes all 25 existing generic rejection
APIs and the separate Scheduled Execution creation rejection. Shared proofs
derive typed call entry, null/quiet/logged behavior, every modeled callback
return and the blocked alternative. Prepared contracts construct the diagnostic
pool and preserve readonly strings. Exact signatures, printers and fragments
use the existing C printer certificates. The fixed actual-file checker derives
membership in the same header signature list before constructing the contract.

Two source consequences connect the same compiled source, numerical C, XML
capability/declaration omissions, adapter bytes, prepared table and literal
pool. They require no extra adapter assumption. The three affected existing
source/history consumers retain their theorem statements. Six backend modules
and one compiler proof module add 35 audit registrations; none are removed.

The owning core/C/FMI/compiler checks passed at 11:19:44 UTC; the required
`nix develop .#verification --command lake test` passed at 12:06:06 UTC on
1103 unchanged inputs. All 418 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Evidence is in
`build/c-factory/public-api-inventory/`: `package-v1.*`, `full-gate-v1.*`,
`integration-v1.json`, `review-v5.json` and `artifacts-v1.*`.

Every retained FMU member, including the native library, is unchanged. The
eFMU changes only generation identities and dependent references/checksums in
three manifests. Numerical C, GALEC and Production C remain unchanged. Existing
artifact/native/rejection checks passed; no grammar, runtime emitter, solver,
metadata behavior or test suite changed. Only these three evidence documents
change after the frozen gate.

These are raw execution contracts. XML omissions do not establish that every
empty Clock, interval or output-derivative request must be rejected. Those
standards findings and complete legal-history correspondence remain open,
together with native/ABI, full provenance, concurrency and MISRA obligations.
K02–K05 still block grammar expansion. No full FMI/eFMI conformance or
CompCert-level whole-compiler claim follows from this increment.

This checkpoint exposed SR09's empty-setter endpoint defect. Its original
review witnesses remain in `empty-setter-review-v1.*` and
`public-coverage-review-v2.json`; the accepted correction and full artifact
evidence are recorded in the SR09 section.

**Absent-variable initialization histories (full gate passed):**

The initialization protocol includes all 24 existing absent-variable accessors.
Empty calls preserve the heap; rejected counts derive Error and retain every
modeled logger return or blocked outcome. Source-bound creation, initialization,
simulation, reset and release compose through recurring ME/CS histories,
including interrupted prefixes. Caller storage, readonly diagnostics, ownership,
logging configuration and numerical source observations are retained.

The owning core/C/FMI/compiler checks passed at 10:19:29 UTC; the required
`nix develop .#verification --command lake test` passed at 11:05:22 UTC on
1096 unchanged inputs. All 194 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Six new audit registrations retain all
previous roots. Evidence is in `build/c-factory/accessor-histories/`:
`package-v1.*`, `full-gate-v1.*`, `integration-v1.json`,
`standards-review-v1.json` and `artifacts-v1.*`. The existing mandatory adapter
field supplies every prepared accessor from the same source artifact.

Every retained FMU member, including the native library, is unchanged. The
eFMU changes only generation identities and dependent references/checksums in
three manifests. Numerical C, GALEC and Production C remain unchanged. Existing
artifact/native/rejection checks passed; no grammar, emitter, solver, metadata
or test behavior changed. Only these three evidence documents change after
the frozen gate.

These are raw execution histories. They do not license null arguments,
terminated-state setters or unrestricted CS getter/setter ordering. Complete
legal-history correspondence, remaining public APIs, native/ABI and provenance,
concurrency and MISRA obligations remain open. K02–K05 still block grammar
expansion; no full FMI/eFMI or CompCert-level compiler claim follows.

**Absent-variable accessors (full gate passed):**

A shared contract covers all 24 emitted Get/Set functions for Float32,
integer, Boolean, String and Binary types absent from the current model.
Empty calls preserve the whole heap. Null/nonempty rejection and every modeled
logger outcome use the actual function table and prepared diagnostic pool.
Binary's separate size array is retained. The actual XML proof also excludes
Enumeration, which shares the Int64 APIs; valid typed selections and consistent
counts derive the successful call without assuming its returned result.

The mandatory adapter contract and fixed checker bind every exact signature,
printed function and runtime contract to the same compiled source, numerical C
and XML. Existing source/history theorem statements remain intact. The owning
core/C/FMI/compiler checks passed at 09:27:21 UTC; the required
`nix develop .#verification --command lake test` passed at 10:12:18 UTC on
1094 unchanged inputs. All 188 selected roots passed without unexpected axioms,
changed-module warnings or input drift. The audit adds 27 registrations and
removes none. The initial failed build and unchanged-statement fixes remain
recorded in `package-v1.*` and `additional-consumers-v1.json`. Evidence is in `build/c-factory/empty-access/`: `package-v2.*`,
`full-gate-v1.*`, `integration-v2.json`, `review-v4.json` and `artifacts-v1.*`.

Every retained FMU member, including the native library, is unchanged. The
eFMU changes only generation identities and dependent references/checksums in
three manifests. Numerical C, GALEC and Production C remain unchanged. Existing
artifact/native/rejection checks passed; no emitter, solver, source grammar or
test suite changed. Only these three evidence documents change after the gate.

This accepts the raw public-call and same-source artifact contracts. It does
not authorize null arguments, setters after termination or arbitrary importer
histories. CS getter-after-setter ordering, complete history composition and
standards correspondence remain open, together with native/ABI, provenance,
concurrency and MISRA obligations. K02–K05 still block grammar expansion.

**Evaluation during initialization histories (full gate passed):**

Evaluation success and rejection now compose through the initialization
protocol, reset/retry, post-exit ME operation and recurring ME/CS runs. The
classifier covers every represented interface/mode pair. The same public C
function derives returned status and memory effects, including every modeled
logger return and the blocked alternative. Original caller/borrowed storage,
ownership, source checkpoints and completed/stopped observations compose from
actual creation through final release.

The common bundle reuses its existing ME evaluation contract. Successful
evaluation preserves state and cannot replace the required discrete update.
The owning core/C/FMI/compiler checks passed at 08:23:37 UTC; the required
`nix develop .#verification --command lake test` passed at 09:17:17 UTC on
1087 unchanged inputs. All 150 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Five new audit registrations supplement
the retained source/history roots. Evidence is in
`build/c-factory/evaluation-initialization/`: `package-v1.*`, `full-gate-v1.*`,
`integration-v1.json`, `standards-review-v1.json` and `artifacts-v1.*`.

Every retained FMU member, including the native library, is byte-identical to
the accepted discrete-evaluation checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC and Production C are unchanged. Existing artifact/native/rejection checks
passed; no grammar, solver, emitter, metadata or test suite was added.
Only these three evidence documents change after the frozen gate.

This closes evaluation interleavings in the represented initialization and
recurring protocols. Remaining public capability/type-access calls, unrestricted
host/callback/concurrent behavior, complete native/ABI and artifact provenance,
MISRA and whole-subset standards obligations remain open. K02–K05 still block
grammar expansion; this is not a full FMI-conformance claim.

**Discrete evaluation (full gate passed):**

The existing evaluation call now accepts only ME Event Mode in this profile.
The actual XML omits the capability, whose reviewed default is false; successful
evaluation preserves the whole heap. It does not complete event iteration.
Null/rejected calls retain every modeled status and logger alternative. The
mandatory adapter/checker binds the exact printed function and common prepared
table/literal pool; the source theorem retains the same numerical C and XML.
ME control and rejection histories, storage frames, creation/release and the
numerical/recurring source consumers carry the strengthened contract.

The owning core/C/FMI/compiler checks passed at 07:31:36 UTC; the required
`nix develop .#verification --command lake test` passed at 08:15:06 UTC on
1085 unchanged inputs. All 133 selected roots passed without unexpected axioms,
changed-module warnings or input drift. The audit adds 21 registrations and
retains all prior roots. Evidence is in `build/c-factory/discrete-evaluation/`:
`package-v1.*`, `full-gate-v1.*`, `integration-v1.json` and `artifacts-v1.*`.

The retained FMU changes only the evaluation guard in `sources/fmi3.c` and its
native library. The eFMU changes only generation identities and dependent
references/checksums in three manifests. Numerical C, GALEC and Production C
remain unchanged. The existing ME native lifecycle check now exercises
Initialization rejection and Event no-op; no new test suite was added.
Only these three evidence documents change after the frozen gate.

This accepts the corrected call and represented ME control/rejection history
composition. It does not close the remaining initialization/public-call
interleavings, unrestricted host/callback behavior, complete native/ABI and
artifact provenance, or MISRA and whole-subset standards obligations.
K02–K05 remain open; no grammar expansion or full FMI-conformance claim.

**Event-indicator histories (full gate passed):** Empty event queries
now compose with initialization, mixed ME operation, reset, creation and release.
Raw observations, original caller/borrowed storage and universal callback
policies determine the source checkpoints and completed/stopped results.

The owning C/FMI/compiler checks passed at 06:36:55 UTC; the required
`nix develop .#verification --command lake test` passed at 07:20:04 UTC on
1079 unchanged inputs. All 63 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Three new audit registrations supplement
the retained history/source roots. Evidence is in
`build/c-factory/event-histories/package-v1.*`, `full-gate-v1.*` and
`integration-v1.json`.

Every retained FMU member, including the native library, is byte-identical to
the accepted zero-event getter checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests; numerical C,
GALEC and Production C are unchanged. See
`build/c-factory/event-histories/artifacts-v1/` and its JSON record.
The existing artifact, importer, native and mutation checks passed; no test
suite was added. Only these three evidence documents change after the frozen gate.

The next discrete-evaluation review found an overbroad lifecycle predicate:
`fmi3EvaluateDiscreteStates` was admitted during Initialization, although the
pinned FMI 3.0.2 call table lists it in Event Mode. Its false capability default
requires an ignored operation there, so generic capability rejection is not
the replacement. An Event-only policy correction and complete no-op call,
metadata, source and control-history drafts are in
`build/c-factory/discrete-evaluation/`; combined production and artifact
acceptance remain pending. No new grammar or numerical capability is admitted.
K02–K05 and the recurring whole-subset standards review remain open.

**Zero-event getter (full gate passed):** Its mandatory adapter/checker
contract now binds the actual public C function, prepared runtime, XML zero-event
count and the same source/Solve product. Complete ME call-memory behavior covers
success, rejection and every modeled logger alternative.

The owning C/FMI/compiler checks passed at 05:43:02 UTC; the required
`nix develop .#verification --command lake test` passed at 06:26:27 UTC on
1078 unchanged inputs. All 40 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Six existing consumers were updated to
unpack the strengthened adapter conjunction; their statements and audit roots
are preserved. Failed integration evidence remains in `package-v1.*`.
Accepted evidence is in `build/c-factory/event-indicators/package-v2.*`,
`full-gate-v1.*` and `integration-fixes-v1.json`.

Every retained FMU member, including the native library, is byte-identical to
the accepted CS checkpoint. Only generation identities and dependent
references/checksums in three eFMU manifests change. Numerical C, GALEC and
Production C are unchanged. See `build/c-factory/event-indicators/artifacts-v1/`
and its JSON record. The existing artifact, importer, native and mutation
checks passed; no test suite was added. Only these three evidence documents
change after the frozen gate.

The later event-history checkpoint above accepts initialization, mixed ME,
creation/release and resource-handoff composition with its own artifact gate.
K02–K05 and the whole-subset standards review still block grammar expansion.

**CS simulation logging (full gate passed):** Recurring source-bound
creation, initialization, simulation, reset and release now use the mixed
numerical/logging history. Access/protocol continuations and unified restart
retain raw records, source observations, stopped prefixes and the last
successful flag update. Original borrowed inputs and universal callback memory
policies remain explicit host-profile obligations.

The owning C/FMI/compiler checks passed at 04:46:54 UTC; the required
`nix develop .#verification --command lake test` passed at 05:28:57 UTC on
1071 unchanged inputs. All 69 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Earlier failed integration attempts
are retained; their fixes preserve the existing numerical interruption audits
and generalize the handoff/restart contracts. Evidence is in
`build/c-factory/cs-simulation-logging/package-v4.*` and `full-gate-v1.*`.
Only the three evidence documents change after the frozen gate.

Every retained FMU member is byte-identical to the accepted ME checkpoint.
Only generation identities and dependent references/checksums in three eFMU
manifests change. Numerical C, GALEC and Production C are unchanged; see
`build/c-factory/cs-simulation-logging/artifacts-v1/` and its JSON record.
K02–K05 and the whole-subset standards gate remain open. The zero-event getter's mandatory checker and artifact acceptance
and the later complete event-history composition are recorded above.

**ME simulation logging (full gate passed):** All remaining
initialization-access/protocol continuation and restart entry points have been
ported. Its prepared logging contract comes from the same source-bound runtime
bundle, and the affected CS caller retains its previous guarantees.
Shared callback effects and ME/CS call proofs now live in separate package
modules. The owning-package checks passed at 03:24:08 UTC, and the required
`nix develop .#verification --command lake test` passed at 04:09:01 UTC on
1062 unchanged inputs. All 89 selected roots passed without unexpected axioms,
changed-module warnings or input drift. See
`build/c-factory/simulation-logging/package-v4.*` and `full-gate-v1.*`.
Only the three evidence documents change after the frozen gate.

Retained FMU members are all byte-identical to the initialization checkpoint.
The eFMU changes only generation identities and dependent references/checksums
in three manifests; numerical C, GALEC and Production C are unchanged.
See `build/c-factory/simulation-logging/artifacts-v1/` and its JSON record.
The CS checkpoint above accepts the later complete source/lifetime composition
and its own artifact gate; the prepared CS logging call alone did not establish
that guarantee. K02–K05 and the whole-subset compliance gate remain open.

**Mutable logging in initialization histories (full gate passed):**
Logging requests now use the existing raw action, reference transition and
completed/stopped history relations. The prepared runtime derives every call,
including validation failure and a callback with no modeled return. Exact
logging-cell updates compose alongside the numerical state; `Retention.to_retains`
recovers the unchanged-field guarantee when no successful update occurs.
Original category arrays and strings, including writable caller storage, are
carried in a read bank. Each earlier call derives its frame under the stated
borrowing guards; the source theorem does not assume future readable inputs.

The source-to-initialization theorem binds the same source, numerical C, XML
logging category and prepared adapter. Actual factory execution now supplies
the borrowed-input frame: readable pointer/character cells cannot alias atomic
reservation flags. Source-bound creation/release, restart, stopped prefixes
and ME/CS handoffs have been ported. Both handoffs use the final logging flag
computed from the initialization history.

CS simulation now retains the read bank through actual steps, failures,
callbacks and resets, under explicit write separation. Universal exact callback
frames supplement the existing typed-storage policy; unchanged types alone
do not preserve borrowed contents.

ME count/nominal and mixed numerical/error/callback frames now retain exact
borrowed contents. The recurring ME/CS contracts compose logging updates across initialization
segments, and their actual factory executions supply the initial input frame.
Suppressed CS certificates now retain exact frames as well as typed storage.

The owning package checks passed at 01:38:40 UTC. The required full
`nix develop .#verification --command lake test` passed at 02:22:20 UTC on
1056 unchanged inputs. All 173 selected roots passed, including 68 newly
registered roots, with no unexpected axioms, changed-module warnings or input
drift. See `build/c-factory/logging-history/package-v1.*` and `full-gate-v1.*`.
Only the three evidence documents change after that gate.

The retained FMU members are all unchanged, including the native library.
The eFMU changes only three manifests' generation identities and dependent
references/checksums; numerical C, GALEC and Production C are unchanged.
Archives and comparisons are in `build/c-factory/logging-history/artifacts-v1/`.
The premise review preserves the explicit borrowing and universal callback
obligations; this acceptance does not establish unrestricted FMI conformance.

Remaining work, in dependency order:

1. Correct the discrete-evaluation lifecycle predicate and bind its no-op
   behavior, false capability default and complete histories to actual source
   artifacts. Retain the distinction between legal and defensive calls.
2. Complete the remaining emitted public-call families, including capability
   rejection and other variable-type accessors, using reusable call contracts.
   Retain every raw return, callback alternative, recovery state and origin.
3. Complete the native/ABI, complete artifact/provenance and MISRA obligations,
   then rerun the whole-subset MLS/FMI/eFMI checklist. Close K02–K05 before growth.

**Public logging configuration (full gate passed):**
The emitted setter and mandatory actual adapter contract now include the
proved comparison/validation loop, printer, XML category and prepared shared
runtime. Legal selections entail the exact flag update and memory frame;
invalid selections retain the original callback policy. The owning-package
gate passed on 1040 unchanged inputs with 58 new and five affected roots.
The required full `lake test` passed on 2026-09-15 at 00:18:22 UTC,
with all 63 roots and no unexpected axioms, changed-module warnings or input
drift. See `build/c-factory/debug-logging/full-gate-v1.*` and `artifacts-v1.*`.
Only the three evidence documents change after that gate.

The FMU changes only the public setter in `sources/fmi3.c`; its native library
and other members are unchanged. The eFMU changes only three manifests'
generation identities and dependent references/checksums.

The initialization-history checkpoint above now accepts the subsequent
capability, original-category-input and recurring source-bound composition.
Mutable logging during CS simulation and the other K02–K05 obligations remain
open; the current work list distinguishes their draft and accepted evidence.

**Nominal runtime and histories (full gate passed):**
The final ignored draft passed across 80 modules and 56 selected roots. The
owning FMI/compiler changes now connect actual nominal C calls, original
storage, compatible caller-buffer aliases, initialization/restart and mixed ME
histories to source/XML observations. Returning and blocked logger outcomes
remain explicit. Seven new FMI modules and 25 new audit roots are integrated.
The owning-package gate passed at 22:10:56 UTC on 1022 unchanged inputs in
`build/c-factory/nominal-history-package-v2.log`, covering all 56 required roots
without unexpected axioms or changed-module warnings. The required full
`lake test` gate then passed at 22:56:23 UTC on 1022 unchanged inputs,
with all 56 required roots. Its log and JSON record are
`build/c-factory/nominal-history-full-gate-v1.*`. Only the three evidence
documents change after the frozen full gate. The mandatory nominal function
contract is stronger, and this gate accepts that extension.

Retained FMU members, including the native library, are unchanged. The eFMU
changes only three manifests' generation identities and dependent
references/checksums; see `build/c-factory/nominal-history-artifacts-v1/` and
comparison records. Next, complete logging configuration and remaining
public-call coverage. K02–K05 still block grammar growth.

**ME count interleavings (full gate passed):** the checked
draft is now integrated into the FMI/compiler packages. It extends the existing
mixed ME execution, source observations, stopped prefixes and recurring
creation/initialization/reset/release proofs. Original caller cells and the
universal callback policy supply every later storage precondition. Nine new
audit roots supplement the retained roots. The FMI/compiler package gate
passed at 21:15:09 UTC on 1015 unchanged inputs, covering nine new and eighteen
affected roots without unexpected axioms or changed-module warnings. Evidence
is in `build/c-factory/me-count-package-v1.log`. The required full `lake test`
gate then passed at 22:01:57 UTC on 1015 unchanged inputs in
`build/c-factory/me-count-full-gate-v1.log`, with all 27 required roots and no
unexpected axioms or changed-module warnings. Only the three evidence
documents change after that frozen gate. Retained FMU members, including the
native library, are unchanged; the eFMU changes only three manifests'
generation identities and dependent references/checksums. See the
`build/c-factory/me-count-artifacts-v1/` archives and comparison records.
The next nominal-query work must connect existing value/metadata proofs to the
shared runtime, later heaps, missing callbacks and complete histories.

**Count-initialization checkpoint (full gate passed):** both count queries
are now actions in the existing initialization protocol. Original caller
`size_t` storage supports later calls without future-heap assumptions.
Successful and rejected call proofs preserve the model, reservation map,
logger configuration and storage needed for recovery. The composed
initialization, creation/release and recurring ME/CS source theorems compile
with these observations and an explicit actual-XML count contract. The full
gate passed at 21:05:03 UTC on 1012 unchanged inputs, including eight new and
twelve affected roots. The later ME simulation/control extension is accepted
by the checkpoint above. Next, complete nominal-query coverage, logging configuration and
metadata-matched optional/type-access paths.
K02–K05 remain open; no new grammar case is admitted.

**Previous count-query checkpoint (full gate passed):** the shared-runtime
success, null, suppressed-logging and arbitrary modeled logger-outcome
contracts are implemented and required by the actual adapter proposition.
Source binding retains the same numerical C, XML, function table and literal
pool. Standards review found that the old count policy also admitted
Initialization, Continuous-Time and Terminated. The policy and reference
predicate now allow only ME Instantiated/Event Mode, with a core rejection
theorem and corrected existing native checks. The required full artifact gate
passed on 1009 unchanged inputs at 19:55:08 UTC, accepting the changed guards
and stronger adapter contract. The history work above extends that checkpoint;
the new history gate also checks the earlier repair and its dependencies.

| Area | Current evidence | What remains |
| --- | --- | --- |
| Production grammar | One Modelica `Real` state with `der(state) = 1`; generic LALR engine for Modelica and GALEC. DFA implementation and generator removed in `2df35d3`. | No new source case is admitted until the closure checklist below passes. |
| Source and numerical core | Source-independent Real semantics, per-IR equation/behavior preservation, checked default initialization, binary64 rounding and the unit numerical C theorem. | Whole-interface observations and source-to-artifact composition. |
| FMI 3 ME/CS | Both interfaces share Solve. Source-bound creation now composes recurring initialization/simulation/reset segments through release for both ME and CS, retaining completed and modeled stopped source observations. Complete CS step, termination, time and ME control-call contracts are mandatory and artifact-checked. | Complete remaining public calls and their source-bound histories, concurrent ownership, translation-unit and ABI correspondence. |
| Initialization | Creation, entry/exit, rejection and optional logging share the actual static runtime and source IVP. The 801-input full gate and 804-input follow-up package audits passed. | Later host histories and callback frames remain in K02/K03; cross-standard correspondence remains in K05. |
| eFMI | Checked DAE → GALEC → Solve Algorithm → Production C path, method/trace proofs, correlated manifests and actual eFMU certificate. | Cross-standard initialization, coding-guideline evidence and final compliance review. |
| Tensor/AD development | Array source-to-Solve, forward derivative/reverse adjoint foundations and several prepared C contracts are checked. | These are development products; the production compiler still rejects the driven/array profiles. See [tensor plan](tensor-ad.md). |

The recurring ME theorem passed the FMI/compiler package gate on 1007 unchanged
inputs in `build/c-factory/me-cycles-package-v1.log`: 20 new and 6 affected
roots, with no unexpected axioms or changed-module warnings. Actual source-bound
creation, initialization, simulation, reset and release share one printed table
and pool. Original caller resources supply every handoff. Completed and modeled
stopped plans retain earlier source observations and initialization checkpoints;
between-cycle reset statuses are derived from complete C contracts. Release
restores original ownership. Importer-selected ME trials carry no claim of
following the exact source IVP. The generic initialization-prefix proof is now
shared by ME and CS without changing the CS theorem's statement.

The count-query work described above follows this ME checkpoint. Close the
remaining public API inventory and integrate those observations into the
source-bound histories. K02–K05 remain open. The ME checkpoint `ddebdc3`
passed the full [GitHub gate 34882266695](https://github.com/CogniPilot/rumoca_lean/actions/runs/34882266695)
at 19:48:16 UTC. The local count-query gate below also checks its dependencies.
No new source case is admitted.

Latest completed main-workspace gate:
`build/c-factory/count-history-full-gate-v2.log`, passed at 21:05:03 UTC with
all 1012 integration inputs unchanged. Eight new and twelve affected audit roots
passed without unexpected axioms or changed-module warnings. The mandatory
actual-artifact checks, both FMU interfaces and eFMU checks passed. Only the
three verification/roadmap documents change after that frozen gate. Retained
archives and member comparisons are under
`build/c-factory/count-history-artifacts-v1/` and adjacent JSON records. Every
FMU member is unchanged from the preceding count-runtime artifact; the eFMU
changes only generation identities and dependent references/checksums in three
manifests. Numerical C, GALEC and eFMI Production C are unchanged.

Earlier main-workspace gate:
`build/c-factory/cs-contract-full-gate-v1.log`, passed with all 869
integration inputs unchanged. It checks the mandatory complete CS call contract,
earlier contracts, both actual FMU interfaces and the eFMU, including the existing
native and rejection controls. Retained archives and comparisons are under
`build/c-factory/cs-contract-artifacts-v1/` and adjacent review files. All FMU
member contents are unchanged from the preceding CS artifacts; the eFMU changes
only generation identities and their dependent references/checksums in three
manifests. Generated numerical C, GALEC and Production C are unchanged.

The subsequent initialization/CS-history/release proofs passed
`lake build check-fmi3 check-compiler` in
`build/c-factory/cs-history-package-v1.log`, with all 877 inputs unchanged.
This follow-up adds derived proofs and audit roots only; it retains the
869-input full-gate evidence for unchanged emission, semantics and mandatory
contracts. The two acceptance snapshots are distinct. No grammar case is added.

The creation follow-up passed the same FMI/compiler package command in
`build/c-factory/cs-created-lifetime-package-v1.log`, with all 881 inputs
unchanged. Nine new audit roots connect the actual source-bound factory to
that CS lifetime. The previous lifetime theorem retains its statement and
reuses the extracted backend composition. Emission, semantics, mandatory
contracts and existing tests are unchanged; their full artifact evidence
remains the 869-input gate. No new full-gate pass is claimed for this follow-up.

`CSProtocol.runtime_create_release` composes actual source-bound creation,
arbitrary finite initialization/CS simulation/reset segments and final release.
It now retains every completed DoStep's actual status/events/heap, source-IVP
sample/error bound and successful outputs, as well as each internal restart's
three returns and initialization-exit source checkpoint. The records refine
the existing raw execution relation with a proved erasure/recovery equivalence.
All reference transitions use the same fixed floating-environment header.
Original storage supplies each handoff and release restores the owner map.

The same source-bound contract now covers every modeled stopped prefix of an
admitted CS plan. Raw interrupted views are equivalent to existing stopped
relations and retain an explicit decomposition of each script. Completed-prefix
certificates preserve readbacks, initialization checkpoints, CS samples/error
bounds and successful outputs, including all earlier cycles. Complete call
contracts rule out a blocked internal restart or between-cycle reset. The
pending action contributes no returned status, output, checkpoint or release;
its recorded heap is the heap before that action.

Nineteen new and eight affected roots passed the 998-input FMI/compiler package
gate in `build/c-factory/stopped-source-package-v1.log`, with no input drift,
unexpected axioms or changed-module warnings. Publication changes only three
documentation files after the frozen gate. The earlier `baeb7bd` revision
passed the full [GitHub gate 34868166166](https://github.com/CogniPilot/rumoca_lean/actions/runs/34868166166)
at 17:24:44 UTC; that result does not establish full-artifact acceptance of
this change. Recurring ME composition and its stopped-source correspondence,
remaining public calls and K02–K05 remain open.

The CS raw restart relation now admits arbitrary returned codes; the complete
call contracts prove that reset, entry and exit succeed. This repairs an
accidental success premise in that raw relation. Returning and blocked action
equivalences and finite-history progress now feed the adapter/source theorem,
which derives arbitrary observed status lists and preserves its source IVP
and error bound. Six new and seven affected roots passed the 985-input
FMI/compiler package gate in `build/c-factory/cs-raw-progress-package-v1.log`.
This is a prerequisite repair for repeated-history composition, not closure
of that task or a new full-artifact gate.

Completed ME, logged CS and suppressed CS histories now supply the
original caller storage, ownership and logger state needed for actual reset
followed by the reusable initialization protocol. Arbitrary selected caller
regions retain object descriptions under universal logger storage policies;
typed output buffers may alias compatibly. The source-bound reset theorem
retains actual statuses, returning/blocked alternatives and exit/source-IVP
checkpoints. Thirty-three roots passed the 984-input C/FMI/compiler package
gate in `build/c-factory/simulation-restart-package-v1.log`. The subsequent
990-input checkpoint supplies that recurring CS composition through release;
the corresponding ME composition remains open. Earlier
simulation relations retain their contiguous restart constructor alongside
these new composition lemmas; no new simulation semantics was introduced.

Actual source-bound creation now supplies the reusable initialization
protocol, including repeated failures, resets and accepted accesses. Completed
initialized histories feed the existing mixed ME and CS runs, with original
caller storage, source observations and release restoring original owners.
The common protected-cell invariant covers scalar outputs and indexed buffers.
The 23 new roots passed the 977-input C/FMI/compiler package gate in
`build/c-factory/created-protocol-package-v1.log`; this remains distinct from
the earlier full-artifact evidence. The subsequent 984-input checkpoint
supplies the simulation-to-reset/protocol handoff. Repeated whole-history
composition, remaining public calls and K02–K05 stay open.

The reusable initialization subprotocol now composes accepted/rejected
Float64 accesses, entry/exit and reset across repeated failed attempts.
`InitializationProtocol.runtime_source` binds it to the actual source, numerical
C, XML and one prepared adapter table/pool. Completed raw scripts derive
statuses/readbacks, finite state, ownership, retained caller storage and actual
exit/source-IVP checkpoints. Progress constructs a complete script or an actual
blocked-call prefix. Factory-invariant and conditional-release lemmas are also
checked. The 35 roots passed the 970-input FMI/compiler package gate in
`build/c-factory/initialization-protocol-package-v1.log`; its review accounts
for the existing audit macro's unquoted name format. This adds derived proofs,
not a new full-artifact result. The subsequent 977-input checkpoint supplies
actual creation, ME/CS execution and release; later restart accesses remain open.

**Distance to expansion:** K01 is closed for its scoped initialization profile;
K02–K05 remain partial or open. Actual creation now composes with initialization,
represented ME numerical/control successes and errors, modeled logging, repeated
reset/reinitialization and mode-appropriate release. Every restart records the
actual initialized heap and its source IVP; later trial-state writes remain
separate from that trajectory. The corresponding CS lifetime covers mixed
accepted/rejected steps, reset/reinitialization and modeled logging outcomes.
Both restore original ownership within their stated contracts.

Both Float64 accessors now have artifact-bound contracts in the same runtime,
retaining represented batches, mixed/repeated read references, exact finite
readback/state writes, empty/null calls, rejection and modeled logging behavior.
Accepted Float64 histories now compose with initialization entry and exit.
Original typed storage supplies every later request buffer and heap. Pre-entry
queries concern state start values; initialization queries evaluate time/state/
derivative values. Actual script observations and the unique source IVP at exit
are derived, including intervening writes. Actual source-bound creation now
supplies the handle/default/storage for those histories, and termination/release
restores the original owners. Mixed CS execution now uses that overridden seed,
covering subsequent successful/rejected steps, reset/reinitialization and both
logging policies through mode-appropriate release. Ten new roots passed the
951-input FMI/compiler package gate in
`build/c-factory/initialization-cs-run-package-v1.log`; this retains the distinct
earlier full-artifact evidence and is not a new full-gate pass.
The corresponding ME continuation now passes the 955-input FMI/compiler
package gate in `build/c-factory/initialization-me-run-package-v2.log`.
It derives Event Mode, initial event-iteration duty, selected state, clock/stop
bound, caller storage and configuration from the actual post-access heap.
Existing mixed histories retain source derivative observations and reset
initialization checkpoints through release restoring the original owners.
Common lifecycle and reset-storage proofs are shared with CS. The six new
roots do not close a whole K02–K05 item or constitute a new full artifact gate.
Rejected Float64 calls now have an actual-source-bound runtime contract:
typed raw caller preparation, independent guard conditions, exact status/events
and recovery storage under both logging policies. Shared reset/reinitialization
now permits accepted access interleavings and derives the new source IVP.
The 31 new roots passed the 963-input FMI/compiler package gate in
`build/c-factory/float64-rejection-package-v2.log`. The subsequent initialization protocol now permits
further rejected accesses during recovery. Its composition with actual creation,
mixed ME/CS simulation, later restarts and release remains the next work.
Remaining public calls still need coverage.
No later heap or successful call may substitute for those composition proofs.
Concurrent instance ownership and the transitive no-heap
policy, complete source-to-artifact/provenance and C-profile correspondence,
and standards/MISRA closure remain required. The final release also requires
independent review and the complete artifact gate at that revision. These are
substantial obligations; there is no defensible coverage percentage or short
completion estimate from the number of audited roots.

The created initialization-access follow-up passed
`lake build check-c check-fmi3 check-compiler` on 947 unchanged inputs in
`build/c-factory/created-access-package-v1.log`. Its 15 new roots derive original
creation/storage, actual accepted initialization observations and source IVP,
preserved atomic ownership, the CS seed/clock/stop/storage handoff, and release.
No future successful C execution is supplied as a premise. Existing semantics,
emission, mandatory artifact contracts and tests retain the separate 869-input
full-gate evidence; this package pass is not a new full-gate result. Rejected
accesses/logging/recovery and later simulation composition remain open.

The 41 accepted initialization-access roots passed
`lake build check-fmi3 check-compiler` on 942 unchanged inputs in
`build/c-factory/initialization-access-package-v2.log`. The source theorem binds
both accessors and initialization to the same actual table/pool and metadata,
constructs execution, and determines every completed script's observations and
source IVP. Original valid instance/storage remain premises. This derived-proof
checkpoint retains the separate 869-input full-gate evidence for unchanged
semantics, emission, mandatory contracts and tests; no new full-gate pass or
K02–K05 closure is claimed.

The six initialization/buffer prerequisite roots passed
`lake build check-c check-fmi3 check-compiler` on 937 unchanged inputs in
`build/c-factory/initialization-prerequisites-package-v1.log`. The existing
semantics, emission, mandatory contracts and tests retain the separate 869-input
full-gate evidence. This does not close initialization-history composition,
K02–K05 or the grammar-expansion gate.

The nine added getter/runtime roots passed `lake build check-fmi3 check-compiler`
on 935 unchanged inputs in `build/c-factory/float64-environment-package-v1.log`.
The common compiler theorem binds both accessors, their numerical helper and
metadata to the same source/table/pool. The separate 869-input full gate and
unchanged archives retain the earlier semantics/emission/mandatory-contract/test
evidence; no new full-gate pass or grammar admission is claimed.

The ten added Float64 setter/runtime roots passed
`lake build check-c check-fmi3 check-compiler` on 933 unchanged inputs in
`build/c-factory/float64-set-environment-package-v1.log`. The generic prefix
transfer, batched setter, suppressed/enabled failures, prepared diagnostics and
source/artifact link are checked. Earlier semantics, emission, mandatory
contracts and tests retain the separate 869-input full gate and unchanged
archives; no new full-gate pass or grammar admission is claimed.

The created mixed ME lifetime passed `lake build check-fmi3 check-compiler`
in `build/c-factory/me-mixed-lifetime-package-v2.log` on 930 unchanged inputs.
Its seven added roots derive configuration and release metadata from the actual
factory and history, restore the original owners, and retain all source/raw
observation guarantees. A common lifecycle suffix handles active and already
Terminated instances. The first package attempt needed an explicit import for
an existing storage lemma. Earlier semantics, emission, mandatory contracts and
tests retain the separate 869-input full artifact gate and unchanged archives;
no new full-gate pass or grammar admission is claimed.

The mixed ME history follow-up passed `lake build check-fmi3 check-compiler`
in `build/c-factory/me-mixed-run-package-v1.log` on 927 unchanged inputs.
Its 15 added roots retain every modeled callback branch, connect actual and
certified returning actions in both directions, and derive raw success/Error
statuses, derivative equations and actual initialization checkpoints. Rejected
setter preparation covers arbitrary IEEE bits. Initial typed storage, reusable
caller buffers and fixed logger configuration remain explicit premises.
Earlier semantics, emission, mandatory contracts and tests retain the separate
869-input full artifact gate and unchanged archives. No new full-gate pass or
grammar admission is claimed; creation/release composition remains next.

The created ME numerical/reset lifetime passed `lake build check-fmi3 check-compiler`
in `build/c-factory/me-numerical-run-package-v1.log` on 919 unchanged inputs.
Seventeen added roots retain recovery storage, expose each of the three restart
call results, derive actual initialization checkpoints and restore original
owners after mixed numerical/reset histories. Earlier
semantics, emission, mandatory contracts and tests retain the separate
869-input full artifact gate and unchanged archives. No new full-gate pass
or grammar admission is claimed for this derived-proof checkpoint.

The ME rejection/recovery follow-up passed the same package command in
`build/c-factory/me-failure-recovery-package-v1.log` on 923 unchanged inputs.
Its 15 added roots share actual request arguments and diagnostics, retain all
modeled callback outcomes, preserve original owners and derive the actual
three-call recovery checkpoint's source initialization. Valid original storage
and the universal external frame remain explicit. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full artifact gate;
this is a recovery building block, not a closed mixed-history gate.

The ME derivative follow-up passed `lake build check-fmi3 check-compiler`
in `build/c-factory/me-derivative-environment-package-v1.log` on 903 unchanged
inputs. Eleven added roots compose actual helper/kernel execution with the
public output/status, retain null/rejection/logging cases on later heaps, and
connect the observed derivative to Solve and the source Real equation. One
actual table and pool now supply both state-access and derivative-access
contracts. Numerical C and derivative/state metadata remain bound to the same
source artifact. Earlier semantics, emission, mandatory contracts and tests
retain the separate 869-input full artifact gate; mixed ME histories remain open.

The ME state-access follow-up passed `lake build check-fmi3 check-compiler`
in `build/c-factory/me-state-environment-package-v1.log` with all 900 inputs
unchanged. Six added roots derive complete getter/setter calls in the same
header/object/literal interface as creation and lifecycle histories, including
all existing rejection reasons and disabled, missing or enabled logger paths.
The actual source-bound accessor fragments and mandatory contracts are retained;
later failures require preserved diagnostic literals. A supplied trial state
does not establish an original-IVP solution. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full artifact gate.
Derivative queries and complete ME numerical histories remain open.

The recovery follow-up passed `lake build check-fmi3 check-compiler` in
`build/c-factory/cs-recovery-package-v1.log`, with all 885 inputs unchanged.
Sixteen added roots connect the required CS rejection contract to actual reset
and initialization in the same header/object/literal environment. The new
source trajectory starts from the Solve default at the new requested time.
Suppressed logging preserves ownership and slot metadata; enabled logging
retains all modeled outcomes and derives recovery conditionally on an explicit
instance-record frame. Earlier semantics, emission, mandatory contracts and
tests are unchanged; their artifact evidence remains the 869-input full gate.
This is a recovery building block, not a complete mixed-history theorem.

The subsequent mixed-history follow-up passed the same package command in
`build/c-factory/cs-run-package-v2.log`, with all 890 inputs unchanged.
Its 25 added roots track lifecycle mode, the current source initial-value
problem, rounded clock, elapsed solver duration and reusable recovery/caller
storage. Successful steps expose all four FMI outputs explicitly. The trace
derives each later heap, preserves diagnostic bytes and atomic reservations,
and retains logger configuration and slot metadata. Its source observation
uses the same AST index as Solve and applies the numerical/clock error bound
to the actual readable state. Earlier semantics, emission, mandatory contracts
and tests are unchanged; the 869-input full artifact evidence is retained.
The theorem uses a fixed typed output-buffer bank (or omitted pointers),
nearest-rounding library observations and suppressed logging. It does not
replace the broader single-call contracts or close the whole lifecycle gate.

The mixed-lifetime follow-up passed the same package command in
`build/c-factory/cs-run-lifecycle-package-v1.log`, with all 893 inputs unchanged.
Its 16 added roots derive creation through mixed stepping/recovery and release
from original storage and ownership. Final Step Mode is terminated before
release; final error/Terminated Mode is released directly. The composed frame
preserves unrelated memory, and release restores the original owners. Source
initialization, successful outputs and the final numerical/clock error bound
remain explicit. Earlier semantics, emission, mandatory contracts and tests are
unchanged, retaining the separate 869-input full artifact evidence. Enabled
callbacks and the other K02–K05 obligations remain open.

The enabled-logging history follow-up passed the same package command in
`build/c-factory/cs-run-logging-package-v1.log`, with all 896 inputs unchanged.
Its 11 added roots preserve every modeled returning callback branch and the
no-return alternative. A universal external frame protects instance/reservation
storage and caller outputs while permitting private logger effects. Actual
completed C-call scripts retain source/numerical guarantees and owners. Earlier
semantics, emission, mandatory contracts and tests retain the separate
869-input full artifact evidence. Creation/release composition for enabled
logging and the other K02–K05 obligations remain open.

The callback-enabled lifetime follow-up passed the same package command in
`build/c-factory/cs-logged-lifetime-package-v1.log`, with all 898 inputs unchanged.
Its three added roots derive creation/initialization, the branching history and
release for every completed actual script. Observed statuses are proved equal
to reference statuses; matching statuses are not an execution premise. Original
owners are restored, with a frame for protected unrelated cells. The callback
frame remains universal and explicit; no return or final heap is presumed for
a blocked callback. Earlier semantics, emission, mandatory contracts and tests
retain the separate 869-input full artifact evidence. Remaining public calls,
ME numerical interactions and K02–K05 still block grammar expansion.

The actual adapter certificate now requires the complete `fmi3SetTime`
contract. Its 25 added roots passed the owning-package and full artifact gates
with 815 unchanged inputs. The history theorem connects each admitted trial-time update to the
reference window while preserving model state and the source initialization
relation. This is no claim that the setter integrates the model.

The current checkpoint additionally requires complete event/continuous entry,
completion and discrete-update contracts in the actual adapter certificate.
Its composed ME control history retains intermediate heaps, output values,
reusable caller storage and the source initialization relation; continuous
entry requires a completed discrete iteration. The 92 added roots passed the
C/FMI/compiler package audit in `build/c-factory/me-package-gate-v5.log`, with
all 829 inputs unchanged. The full artifact gate also passed for that exact
snapshot; only these three status documents changed afterward. Integration
with importer state updates, numerical queries, creation, errors and concurrent
histories remains open.

The derived lifecycle follow-up connects both initialization calls, admitted
ME control histories, termination and release with the original host lease.
It derives the continued ownership and caller-buffer invariants, retaining
source initialization, exact calls/outputs and the final memory frame. Its 19
new roots passed the C/FMI/compiler package audit with 835 unchanged inputs in
`build/c-factory/me-lifecycle-package-gate-v1.log`. This leaves emitted code
and mandatory artifact contracts unchanged; the preceding full gate supplies
their artifact evidence, with the derived-proof snapshot recorded separately.
The next five-root checkpoint connects this lifecycle to actual public creation,
deriving the selected handle, source default and caller-buffer validity from
available initial storage. Release restores the original owners and the final
frame covers the complete creation-to-release chain. The FMI/compiler audit
passed in `build/c-factory/me-creation-package-gate-v1.log` with all 838 inputs
unchanged. Importer state/numerical interactions remain open.

The C conversion checkpoint replaces integer `0`/`1` special cases with a
proved exact encoder for magnitudes below `2^53`, and adds checked finite
Float64→unsigned-size truncation. The 32 core/C roots include actual expression
evaluation. The core/C/FMI/eFMI/compiler audit passed in
`build/c-factory/c-integer-package-gate-v3.log` with all 840 inputs unchanged.
The renewed full artifact gate passed in `build/c-factory/c-integer-full-gate-v1.log`
with the same 840 inputs unchanged. Both checked archives are retained under
`build/c-factory/c-integer-artifacts-v1/`; C/header/GALEC and FMI XML match the
ME checkpoint, with only fresh eFMI generation identities and dependent checksums.
The emitted code, grammar and mandatory contracts are unchanged. CS library
calls, overflow/status paths and repeated-step refinement remain open.

The next derived-proof increment integrates finite binary64 floor, ordinary
math-library call contracts, the actual `model_advance` helper and source error
at a separately reported time. Repeated Solve calls compose over an unbounded
mathematical duration while each C count remains bounded. These 27 roots are
in their owning core/C/FMI/compiler packages. The package audit passed in
`build/c-factory/cs-prerequisites-package-gate-v1.log` with all 845 inputs
unchanged. Earlier semantic definitions, emitters and mandatory contracts are
unchanged, retaining the preceding full artifact evidence; the full gate was
not rerun for these derived proofs. These prerequisites do not establish the
public `fmi3DoStep` call.

The arithmetic checkpoint gives every pair of finite addition operands a
result, including signed infinity on overflow. An independent Real/rounding
relation characterizes the result and its encoding, and C proofs cover both
member-read and prepared-register expressions. Earlier finite-result theorem
statements remain intact. This addresses the sum-before-cap semantic gap
without changing generated C or rejection order; public-call composition is
still required. Its 21 added roots passed the core/C/FMI/eFMI/compiler audit in
`build/c-factory/finite-addition-package-gate-v1.log` with all 847 inputs
unchanged. The renewed full artifact gate passed in
`build/c-factory/finite-addition-full-gate-v1.log` with the same 847 inputs
unchanged, including the two overflow cases added to the existing native FMI
check. Both checked archives are retained under
`build/c-factory/finite-addition-artifacts-v1/`. C/header/GALEC and FMI XML
match the preceding artifacts; only eFMI generation identities and their
dependent checksums changed. Complete public CS execution remains open.

The next derived-proof increment connects ordinary external calls to fresh
local declarations, and the CS duration checks to a unique positive bounded
solver count. It derives the C count conversion and finite clock sum, while
retaining the separate progress guard. The actual solver/time/output suffix
derives the nested helper execution and exact state, clock and output writes,
with an explicit memory frame. These 14 roots passed the core/C/FMI/eFMI/compiler
package audit in `build/c-factory/cs-duration-package-gate-v2.log`, with all
850 inputs unchanged. No emitter, existing
semantic definition or mandatory artifact contract changes. Full public
admission, rejection/logging and repeated-step composition remain open.

The rounding-environment follow-up supplies an explicit signed-32-bit
`FE_TONEAREST` header value and proves the ordinary observation/branch prefix,
including negative failure observations. A reusable closed-body call transfer
preserves compatible interface bindings without requiring agreement on other
functions. The actual adapter's ME quiet-time calls, time-history/source frame
and numerical helper now have consequences in the same header/object/literal
environment. These 14 added roots passed the core/C/FMI/eFMI/compiler package
audit in `build/c-factory/rounding-environment-package-gate-v1.log`, with all
854 inputs unchanged. Only the three status documents changed afterward;
the full artifact gate was not rerun for these derived proofs.
No existing semantic definition, emitter or mandatory artifact contract changes.
Native header correspondence, mode stability/restoration and full public CS
execution remain open.

The next CS increment emits ordinary `fegetround` and `floor` calls into fresh
function-scope locals. Named rounding/clock/grid/solver sections retain the
sum-before-stop-before-discard ordering. Eight new roots prove every finite
sum's guard destination, including overflow, and compose admitted numerical
execution through the actual solver and final state/clock/output writes.
The solver count follows from the duration checks. The core/C/FMI/eFMI/compiler
package audit passed in `build/c-factory/cs-ordinary-package-v1.log`, with all
855 inputs unchanged. The renewed full artifact gate passed with the same
855 inputs unchanged, including both actual archives and all 13 existing
native FMI checks. Retained archives and exact member comparisons are under
`build/c-factory/cs-ordinary-artifacts-v1/`; the FMI adapter source and binary
changed, while numerical C, headers, FMI metadata, GALEC and eFMI Production C
are unchanged. The eFMI manifests change only generation identities and
dependent checksums. Public output setup, input/lifecycle admission,
complete rejected-call logging and repeated-step histories remain open; the
suffix theorem does not close K03 or authorize grammar expansion.

The subsequent public-entry increment adds complete successful and null-handle
`fmi3DoStep` proofs. An independent input predicate and its actual guard theorem
classify every raw point/step encoding; the public prefix preserves exact output
initialization on both admission and input rejection. Success derives the
solver count and complete state/clock/output writes with a memory frame.
Sixteen added roots passed the FMI/compiler package audit in
`build/c-factory/cs-entry-package-v1.log`, with all 856 inputs unchanged.
Earlier semantics, emitters and mandatory artifact contracts are unchanged;
the preceding full gate supplies their artifact evidence. Complete rejected
calls/logging, repeated histories and mandatory public-CS artifact composition
remain open. These proofs do not close K03 or authorize grammar expansion.

The error-context follow-up generalizes the existing failure-helper proofs
through checked type, literal and local-name agreement. Static objects and
explicit rounding headers reuse the same callback reasoning; sixteen existing
call sites preserve their public contract statements. New statement contracts
compose after ordinary calls. Complete CS lifecycle rejection now covers
all represented forbidden kinds/modes, raw numerical arguments and nullable
outputs, with enabled/suppressed logging and every represented callback outcome.
Eleven added roots and the generalized existing roots passed the FMI/compiler
package audit in `build/c-factory/cs-errors-package-v1.log` with all 858 inputs
unchanged. Emitters, earlier semantics, mandatory artifact contracts and tests
are unchanged. The following argument-error increment adds complete public
missing-output and invalid-numerical-input calls, with enabled/suppressed
logging and exact output initialization. Twelve added roots passed the
FMI/compiler package audit in `build/c-factory/cs-arguments-package-v1.log`
with all 859 inputs unchanged. Existing error and lifecycle proofs reuse the
new direct-prefix bridges without changing their propositions. Rounding/stop/
discard calls, repeated histories and mandatory CS artifact composition remain
open. This follow-up leaves emission, earlier semantics and mandatory contracts
unchanged and retains the preceding full artifact evidence.

The rounding/stop follow-up adds complete public calls for rejected rounding
observations and stop-limit violations, including overflowing finite-operand
clock sums. Enabled and suppressed logging retain exact output writes and all
represented callback outcomes. A shared admitted-entry prefix and error-path
composition reuse existing body and ordinary-call proofs. Eleven new roots
passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-failures-package-v1.log`, with all 860 inputs unchanged.
Every earlier declaration, emitter and mandatory artifact contract is retained;
the preceding full artifact evidence still applies. Discard, the mandatory
complete CS contract and repeated histories remain open.

The discard/input-partition increment closes both complete public discard paths
and proves that every raw request belongs to exactly one admission case.
Suppressed discard preserves the instance and initializes caller outputs;
logged discard retains all represented callback outcomes. Accepted cases derive
exact finite encodings, duration admission, clock progress and the stop bound.
Sixteen added roots passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-cases-package-v1.log` with all 863 inputs unchanged. Earlier
declarations, emitters and mandatory artifact contracts are unchanged, retaining
the preceding full artifact evidence. At that checkpoint, making the public
cases mandatory and composing repeated histories remained open.

The current increment makes all eight raw CS admission cases mandatory in
`AdapterContract`, with complete accepted/null/suppressed/logged call behavior
in the prepared static interface. Its 18 added roots passed the full 869-input
artifact gate. A further 24 derived roots compose both initialization calls,
any finite accepted CS request history, termination and atomic release. Initial
storage and ownership supply every later heap/lease premise. The result retains
exact Solve state, rounded clock/output writes, the original source IVP and a
bound separating numerical error from clock drift. Those derived roots passed
the 877-input package gate. At that checkpoint, composing creation remained
open. The subsequent nine-root, 881-input package gate closes that composition:
the actual factory supplies the handle, finite Solve default, typed storage
and reservation, and release restores the original owner map. Both lifetime
theorems reuse the same backend composition. Interspersed rejected/logged/reset
calls, concurrent hosts and native header/layout correspondence remain open;
K02–K05 are not closed by this accepted sequential lifetime.

The required adapter certificate includes the static declarations and initial
creation/release contract. Derived theorems connect source identity, optional
logging, rejection/exhaustion, reusable ownership and both successful and
rejected initialization to the same actual function table. They retain exact intermediate heaps,
clock, lifecycle mode and the Solve/source initial value. Complete public
histories, callback frames, concurrent execution, transitive allocation policy,
native ABI and MISRA correspondence remain open.

Exact theorem/evidence history is in [verification.md](../docs/verification.md),
[FMI contracts](fmi3/contracts.md), [standards review](standards-review.md) and
Git history.

## Design constraints

- **No dynamic allocation in generated C.** State and scratch sizes are known
  before execution. The shared Solve/C kernel and eFMI entry points consume
  supplied storage. FMI uses bounded preallocated instance storage without
  changing its standard ABI or reducing the project to a single-instance model.
  The current FMI emitter uses 32 permanent slots. Complete execution,
  concurrent ownership and a transitive allocation policy remain required.
- **Suitable for RTOS integration.** The numerical path has no OS services,
  heap calls, hidden locks or incidental I/O. Prove operation/storage bounds;
  record target timing, stack use and integration assumptions separately.
  Do not describe host benchmarks as WCET evidence. Static-pool synchronization
  belongs to instance acquisition/release, outside numerical stepping.
- **MISRA C compliance is required for generated products.** Use the supplied
  MISRA C:2025 as the primary review baseline with the existing C11 profile;
  map eFMI's older references separately. Include shared C,
  FMI/eFMI adapters, generated headers and the applicable integration boundary.
  Prefer formally checked rules; process directives, adopted headers and any
  deviations need explicit evidence. A Lean proof or analyzer pass alone does
  not establish whole-product compliance. The rule inventory is still open.
- Solve owns the executable IVP. Preserve tensor rank, extents, operations and
  provenance through indexed IRs; do not enumerate tensor elements in lowering.
  `backend-c` consumes prepared Solve. FMI follows DAE → Solve; eFMI follows
  DAE → GALEC → Solve Algorithm. Neither backend resolves names, infers shapes,
  chooses a solver or repeats DAE work. Compare against `~/git/rumoca` at each
  stage; the standards remain authoritative.
- Keep the compiler, EBNF tooling and proofs in Lean, using mathlib where
  appropriate. Retain reusable LALR parsing, typed frontend actions, required
  origins, independent package builds and native Lake proof reuse.

## Closure checklist before grammar growth

These five work packages form the critical path. Their scope is the entire
currently admitted subset, including supported and rejected interface calls.
Dependencies order implementation; specification review can proceed alongside
proof work. Do not replace an unfinished requirement with a smaller claim.

### K01 — Finish initialization evidence

**State:** complete for the scoped initialization increment. SR05 is resolved;
SR08/S01 and whole-stage verification remain open.
**Existing IDs:** S01, F02, F03, SR05, SR08.

- [x] Finish the existing `lake test` process and confirm its source inventory
  stayed unchanged. Retain the actual FMU/eFMU and compare changed code members.
- [x] Record artifact-bound entry/exit, arbitrary raw-argument rejection,
  logging, frame and initialized-source consequences. Review the inclusive
  start/stop policy against the pinned FMI clauses and close only that SR05
  finding when supported by evidence.
- [x] Preserve the distinction between a source `Real` initial-value choice,
  the compiler's diagnosed zero fallback and a finite FMI host-set value.
  The remaining common FMI/eFMI initialization argument belongs to K05.

**Exit evidence:** `initialization_source`, mandatory `AdapterContract`
initialization field, unchanged axiom audit, full-gate result and retained
actual artifacts. Initialization success does not close lifetime or all of F02.

### K02 — Replace heap allocation with proved static instance storage

**State:** static runtime integrated and artifact-checked in the main
workspace; complete runtime/history and no-heap/MISRA closure remain open.

The runtime emits 32 permanent ME/CS slots. Its mandatory declaration and
initial creation/release contract passed the full artifact gate with 793
unchanged inputs. Thirteen later derived roots have focused package evidence,
including the 798-input public-factory audit: actual-source/literal linkage,
quiet/logged exhaustion, all input rejection causes, immediate creation/release,
reusable ownership and the stored Solve/source initialization value. The
renderer and earlier contract definitions are unchanged by those follow-ups.
The earlier published `2628f35` used the allocating emitter. See
`build/c-factory/static-runtime-review-v1.md` for exact evidence and boundaries.

Creation now supplies the premises of Enter/ExitInitialization in the same
object-aware program. Seventeen added audit roots include a shared local-body
bisimulation, complete successful/null public initialization calls and a
source-to-creation/initialization consequence retaining exact heaps, clock,
lifecycle mode, lease metadata and ownership. The C/FMI/compiler audit passed
with 801 unchanged inputs; a focused compiler audit passed the strengthened
postconditions. See `build/c-factory/static-initialization-packages-v1.log` and
`static-initialization-packages-v2.log`. No old contract or emitter changed.

Rejected initialization and its callback paths now have the same object
interface and actual function table. The 22 additional audit roots also cover an
enabled logging flag with a missing logger, and proves the complete logging
case split. Its focused FMI/compiler audit passed with 804 unchanged draft
inputs; the earlier main artifact gate remains the 801-input checkpoint.
No emitter or mandatory contract changed in this derived-proof follow-up.

Reset's complete successful/null calls and reset followed by both initialization
calls now share this object interface. The 15 added audit roots preserve exact
heaps, the Solve/source default, slot metadata, ownership flags and nested
fields in every other element of the same instance array. The FMI/compiler
package gate passed with 806 unchanged inputs in
`build/c-factory/static-reset-package-gate-v1.log`; this is another derived-proof
follow-up with unchanged emission and mandatory artifact contracts.

Termination's complete contract is now required by the actual adapter and its
809-input full gate passed. A further four derived roots compose termination
and release, deriving the later metadata/flag premises from the original lease.
The FMI/compiler package audit passed with 811 unchanged inputs; no emitter or
mandatory contract changed in that follow-up.

Actual CS and ME creation now supplies the lease for their covered mixed
success/error/reset lifetimes and release, restoring the original owner map.
The latest ME derived package gate passed on 930 inputs; the mandatory-contract
full gate passed on 869. Remaining public and initialization interactions and
actual concurrent ownership histories still need composition. Native callback
correspondence, the transitive no-heap and acyclic call graph, and native
profile/layout remain open.
The combined exit items below remain open until all their obligations are met;
no broader item is closed by a sequential initialization prefix.
**Existing IDs:** C01, C02, F02, F03, S03; new no-heap/RTOS requirement.

The shared C machine now has cell-domain/type/permission preservation proofs,
and `StaticSlots` supplies a bounded serial reservation reference with exclusion,
frame and reuse proofs. These are prerequisites, not a completed native storage
implementation: ownership by a particular caller and concurrent C refinement
remain open. A failed serial scan proves exhaustion only for its fixed snapshot.
The shared explicit-null guard and these prerequisites have 44 added roots
and a passing full artifact gate in `build/c-static-storage/full-gate.log`,
with 710 unchanged source inputs. This does not close any K02 exit item.

- [x] Complete artifact verification of the nested aggregate address correction.
  `CMemory.Address` now retains the outer index at each member selection.
  Ten added roots prove exact index/member recovery, tensor-region frames,
  arbitrary member-depth separation and preservation of another record by
  the actual cell store. All affected packages pass in
  `build/c-static-storage/address-package-v3.log`. The required main artifact
  gate passed in `build/c-subobjects/full-gate.log`, including both target
  archives with all 711 source inputs unchanged. Every generated C/header/GALEC
  byte is unchanged from `b478606`. This repairs the prior collision between
  `instances[1].x[0]` and `instances[0].x[1]` in the authored model; valid bounds,
  leaf types and native layout remain separate K04 obligations.
- [ ] Define the storage contract and generation-time instance capacity.
  Preserve multiple independent ME/CS instances. Check capacity exhaustion,
  initialization failure and reuse against FMI; do not add an unstated
  serialization restriction or silently change capability flags.
- [x] Prove the fixed-storage reservation helper in the authored C machine.
  Atomic Boolean exchange/store now have typed call contracts. The actual
  bounded helper has fresh-parameter, initialization, caller-continuation,
  termination, exact sequential-result, frame and certified-printer proofs;
  its result refines the independent slot reference. All affected package
  checks pass in `build/c-atomics/package-check.log`, with 38 added audit roots
  and none removed. The required main artifact gate passed in
  `build/c-atomics/full-gate.log`, with all 720 inputs unchanged and both
  actual target archives checked. Their C/header/GALEC members are unchanged
  from `a1ceae5`. The helper is
  not yet used by the production factory. Shared native execution, ownership,
  declarations and creation/release composition remain exit requirements.
- [ ] Implement activate/initialize/deactivate over a fixed array of fully
  typed instance objects whose storage exists throughout execution. A custom
  allocator over a static byte arena is not a workaround for Dir 4.12.
  Specify concurrency/ownership semantics for shared bookkeeping. Prove bounds,
  unique live ownership, instance isolation, full reset on reuse and failure
  preservation. Model caller misuse and callback assumptions explicitly.
- [x] Complete actual-artifact verification of the identity-validation helper.
  The generated factory now calls a private helper with explicit string calls
  and null checks. Complete execution, unchanged memory and certified printing
  are proved. The mandatory adapter contract locates its exact fragment in the
  rendered file, uses that same definition table, and constructs a consistent
  library environment. All sign-correct `strcmp` results are covered. Package
  checks and the full artifact gate pass with 743 unchanged inputs. Native string-library and
  header correspondence, caller-buffer validity and the enclosing factory's
  execution remain separate obligations.
- [ ] Prove the actual C creation/release functions, including name/token
  validation and logging. Establish the storage premises of every downstream
  public-call theorem from creation. No successful C execution may be supplied
  as a premise in place of this proof.
- [x] Complete artifact verification of public factory admission/rejection.
  Fresh parameter binding, the CS capability guard, null/nonnull identity
  decisions and optional logging are proved. The mandatory contract binds both
  exact public signatures/fragments and their prepared pool to the actual
  definition table. The source consequence derives complete token bytes from
  parsed identifiers. Package audits and the full artifact gate pass with 760
  unchanged inputs. All retained C/header/GALEC members match `13fb2a6`.
  This does not prove successful slot activation, creation/release or the native
  callback/ABI boundary, and does not remove `calloc`/`free`.
- [ ] Bind static declarations, layout, sizes/alignment and handle mappings to
  generated bytes and the chosen C profile. Prove a checked no-heap policy
  over the complete generated call graph, with named external boundaries.
  A search for `malloc` is only discovery evidence, not the contract.
  The reusable decidable `CCallPolicy.NoHeap`/`Acyclic` policy (`packages/backend-c`,
  `RumocaC/NoHeapPolicy.lean`) classifies every callee against a named boundary
  set (defined functions, declared kernel entries, header FMI functions, named
  externals), rejects every allocation entry point and proves the direct-call
  graph acyclic by a topological rank; `noHeap_no_alloc_call` shows a call
  scheduled from a checked body never names an allocation symbol, over the
  machine's own call step rather than a text search. It is instantiated for the
  scalar adapter (`CallPolicy.unit_no_heap`/`unit_acyclic`) and carried as the
  `no_heap_acyclic` conjunct of `FMI3.SourceBuildContract` on the actual bytes.
  The same policy is instantiated for the tensor adapter function list
  (`TensorCallPolicy.tensor_no_heap`/`tensor_acyclic`, boundary set `bTensor`) and
  carried as the `no_heap_acyclic` conjunct of `Rumoca.TensorSourceBuildContract`.
  Still open: the layout/size/alignment binding of static declarations to
  generated bytes is a separate obligation and is not discharged; the numerical
  kernel profile needs its own body-level policy discharge.
- [ ] Keep the RTOS kernel callable with supplied state/scratch; extend the
  existing artifact/native boundary checks for the changed storage mechanism.

**Exit evidence:** actual-function and lifetime/history theorems; certified
storage/call-graph policy in the artifact contract; both FMI interfaces and
eFMI artifacts pass the required gate. Dynamic allocator modeling is not the
next task. Any reusable storage/frame draft is only a prerequisite.

### K03 — Complete public FMI execution and histories

The legal-importer boundary follows FMI §2.2.1: logger callbacks must not
reenter the FMU, and the host prevents races when calling one instance.
Supporting forbidden logger reentry is not an exit requirement. Native callback
correspondence and shared-pool concurrency remain explicit obligations; see the
current [standards interpretation](standards-review.md).

The accepted mixed ME numerical/reset lifetime passed the 919-input FMI/compiler
gate, followed by rejection/recovery on 923, mixed histories on 927 and their
actual creation/release composition on 930 inputs. One actual table/pool supplies
the numerical, rejection, logging and recovery calls. Accepted Float64 initialization
histories now have separate source-bound composition from original valid
instance/storage. Source-bound creation and release now compose with those
accepted access histories on 947 checked inputs. Their mixed CS continuation
now passes on 951 inputs, including rejected steps, reset/reinitialization and
both logging policies. Their mixed ME continuation now passes on 955 inputs,
including actual source observations, reset checkpoints, retained caller/configuration
storage and release to the original owners. Rejected Float64 calls and shared
reset with initialization accesses now pass on 963 inputs. Their actual caller
transfers, raw statuses, callback frames, retained recovery buffers and source
IVP are proved. The 970-input protocol permits further failures during recovery;
the 977-input creation/ME/CS composition supplies actual initial storage and
release. Access interleavings at later simulation restarts and remaining public
interactions are still required. No emitter or mandatory contract changed,
and no new full-gate pass is claimed.

**State:** partial; substantial body and helper proofs can be reused.
**Existing IDs:** F01, F02, N01, N02.

Termination now has a mandatory actual-adapter function
contract, including all represented success/null/rejection/logging cases in
the static interface. Its source consequence composes initialization through
termination and preserves the model/clock and neighboring records. Its 15 new
roots and the full artifact gate passed in
`build/c-factory/termination-full-gate-v1.log`. Four later roots compose
termination/release with exact heaps, lease discharge and a combined frame;
their owning-package audit passed with 811 unchanged inputs. The emitter is
unchanged. These finite call sequences do not cover arbitrary intervening
simulation or concurrent host histories.

- [x] Bind the existing complete Float64 setter to the creation/lifecycle
  runtime and actual source/metadata/table/pool. Preserve arbitrary represented
  batches, validation-before-write, all existing rejection cases, absent/disabled
  logging and every modeled callback outcome. The ten added roots passed the
  933-input C/FMI/compiler package gate; getter and initialization-history
  composition remain open.
- [x] Bind the complete existing Float64 getter and numerical RHS helper to
  the shared runtime, then combine both accessors with one actual source,
  metadata document, function table and pool. Preserve mixed/repeated queries,
  output frames, empty/null calls, existing rejections and modeled logging.
  The nine roots passed the 935-input FMI/compiler package gate; initialization
  histories still need their actual post-access exit and source IVP proof.
- [x] Compose accepted batched Float64 reads/writes before and during
  initialization, deriving original-to-current buffers, complete calls,
  readback and the unique source IVP at actual exit. The 41 roots passed the
  942-input FMI/compiler package gate. Exact compiled source/numerical C/XML/
  adapter table/pool supply the contracts; raw script execution is constructed
  and every completed script has the expected observations. This still assumes
  original valid instance/caller storage; the following item derives it from
  creation. Rejected accesses/logging/recovery remain open.
- [x] Derive original access-history premises from actual source-bound ME/CS
  creation and compose mode-appropriate termination/release. Determine every
  completed accepted initialization script's source IVP and raw observations,
  retain typed storage/reservations and restore the original owners. The CS
  handoff derives seed, clock, stop and original output storage after intervening
  writes. Fifteen roots passed the 947-input C/FMI/compiler package gate. Later
  simulation and rejected/logged/recovery interactions remain separate work.
- [x] Connect the created initialization-access prefix to mixed CS histories
  with suppressed/missing and enabled loggers. Reuse the existing action/trace
  relations, derive observed statuses and the selected source epoch/sample,
  and compose release back to original storage/ownership. Ten new roots passed
  the 951-input FMI/compiler package gate. Later resets retain their existing
  contiguous three-call protocol; access interleavings at those restarts and
  rejected accesses during initialization remain open.
- [x] Connect the created initialization-access prefix to mixed ME histories.
  Derive the Event Mode state, clock/stop/event-iteration invariant, caller
  storage and original logger configuration at actual exit. Retain raw statuses,
  source derivative observations, reset initialization checkpoints and release
  to original owners under the existing universal external frame. Six new
  roots and affected CS roots passed the 955-input FMI/compiler package gate.
  Later restart access interleavings and rejected initialization accesses remain
  open; no additional source trajectory claim applies to importer trial states.
- [x] Prove source-bound rejected Float64 calls and a shared reset operation
  with accepted initialization-access interleavings. Derive typed raw caller
  transfers, complete error/logging behavior, status/events, protected recovery
  buffers and ownership. Reuse the existing initialization certificate to prove
  actual reset/access observations and the unique source IVP at recovery exit.
  Thirty-one roots passed the 963-input FMI/compiler package gate. Original
  instance/reset storage and the universal callback frame remain explicit;
  composition into created/repeating histories and later release is still open.
- [x] Compose a reusable initialization subprotocol with arbitrary finite
  accepted/rejected Float64 access interleavings, separate enter/exit calls and
  repeated resets. Derive later caller storage, observed statuses/readbacks,
  initialization configuration, ownership and unique source IVPs at actual
  exits; preserve a real blocked-call prefix when logging cannot return.
  Thirty-five roots passed the 970-input package gate. Initial valid instance
  storage remains explicit; factory-invariant and conditional-release lemmas
  do not yet compose the whole source-bound creation/simulation lifetime.
- [x] Integrate that subprotocol with actual source-bound creation and the
  existing ME/CS simulation histories. Derive the actual initial handle/default,
  selected run state/clock, caller storage and configuration; retain source
  checkpoints/observations and release to the original owners. The protected
  storage invariant includes scalar outputs and indexed buffers. Twenty-three
  roots passed the 977-input C/FMI/compiler package gate. The same printed table
  and pool supply the contracts; this is not a new full-artifact result.
- [x] Derive actual reset and reusable initialization after completed ME,
  logged CS and suppressed CS histories. Preserve original caller regions
  under universal logger-storage policies, including compatible output aliases.
  Retain actual reset/access statuses, blocked prefixes and exit/source IVPs.
  Thirty-three roots passed the 984-input C/FMI/compiler package gate. The
  source/artifact environment supplies the universal initialization contract;
  no future valid buffers or successful call are supplied by the host.
- [x] Remove successful return-code premises from the raw CS restart relation.
  Derive all three codes from actual C contracts; characterize returning and
  blocked actions and prove finite CS history progress without callback
  totality. Expose progress and derived raw statuses in the adapter/source
  theorem. Six new and seven affected roots passed the 985-input package gate.
- [x] Compose repeated CS initialization/simulation segments through final
  release in one source-bound history theorem. Derive creation/defaults,
  original caller storage, actual handoffs, raw statuses and source checkpoints
  for explicit initialization protocols; retain segment-final source samples
  and restore original ownership. Progress retains real blocked prefixes.
  Fourteen new roots passed the 990-input package gate. Existing raw relations
  and action contracts are reused; no future storage or call success is assumed.
- [x] Complete the corresponding ME recurring initialization/simulation/release
  theorem. Actual creation, repeated handoffs, resets and final release share
  one source-bound table/pool and the original caller bank. Preserve derivative
  observations, initialized source IVPs, raw statuses, ownership and memory
  frames. Twenty new and six affected roots passed the 1007-input package gate;
  this is distinct from full-artifact acceptance.
- [x] Lift every completed CS step and internal restart checkpoint into the
  recurring source trace. Prove raw record erasure/recovery, preserve exact
  statuses/events/heaps, annotate the same fixed-header reference transitions,
  and derive source samples/error bounds and successful outputs at each step.
  Internal restart retains all three public calls and its exit/source IVP.
  Fifteen new and eleven affected roots passed the 994-input package gate.
- [x] Prove source correspondence for all modeled stopped prefixes of admitted
  CS plans, including initialization and earlier completed cycles. Retain raw
  stopped/interrupted equivalences, exact script prefixes and completed source
  observations without assuming callback return. Exclude partially blocked
  internal restarts and blocked between-cycle resets using complete call
  contracts. Nineteen new and eight affected roots passed the 998-input package
  gate. Native hang behavior and callback termination remain outside this model.
- [x] Carry completed and modeled stopped ME observations into the recurring
  source theorem. The interrupted/stopped views are equivalent and retain all
  earlier cycles; complete C contracts exclude a blocked between-cycle reset.
  Source evidence covers derivatives and initialized IVPs, without asserting
  that importer trial states solve that IVP. Included in the 1007-input gate.
- [ ] Inventory every emitted API against metadata: complete success, null,
  invalid-argument/lifecycle, unsupported-capability, logging and return cases.
  Register mandatory contracts for every remaining public function.
- [x] Require complete termination calls and their represented errors/logging
  in the actual adapter contract; compose initialization→termination and
  termination→release with the same definitions, heaps and ownership.
- [x] Accept the mandatory complete ME time-call contract through the full
  artifact gate. Its 25 added audit roots and full 815-input gate have passed;
  successful/null/rejected calls and both logging paths use the static interface.
- [x] Accept the complete ME event/continuous entry, completion and discrete
  update contracts through the full artifact gate. The current checkpoint
  requires their success/null/rejection/logging cases and composes quiescent
  control histories with explicit event-iteration readiness and reusable
  caller buffers. Package and full artifact acceptance passed with 829
  unchanged inputs; both checked archives are retained.
- [x] Derive complete actual continuous-state getter/setter contracts in the
  shared header/object/literal environment on later heaps. Retain success/null,
  lifecycle/access/non-finite failure and every modeled logging outcome. Bind
  both actual fragments and pool to the original source/Solve product. The six
  added roots passed the 900-input FMI/compiler package gate; derivative query
  transport and history composition are separate remaining obligations.
- [x] Derive the complete derivative getter in the shared runtime, including
  actual helper/numerical C execution and all null/rejection/logging cases.
  Supply state and derivative contracts from one actual table/pool and connect
  the observed finite derivative to Solve, source equations and artifact
  metadata. The eleven roots passed the 903-input FMI/compiler package gate.
- [x] Compose finite admitted control/state/derivative histories in the shared
  compiled environment. Derive actual caller buffer writes, statuses, raw query
  outputs, intermediate typed storage, diagnostic preservation and memory
  frames. The actual execution relation assumes no expected outputs; every
  returned derivative agrees with the source Real equation. The 24 roots passed
  the 910-input FMI/compiler package gate. Initial storage remains a premise.
- [x] Compose actual creation and initialization with accepted mixed ME
  control/state/derivative histories, termination and release. Derive all later
  storage, observations and ownership from original available storage, and
  restore the original owners on release. Retain the source initialization
  relation at the initialized heap and source equation agreement for every
  derivative query. The eleven roots passed the 914-input package gate.
- [x] Compose repeated reset/reinitialization with accepted ME numerical
  operations from creation through release. Preserve writable recovery storage,
  derive the statuses of reset and both initialization calls, and prove source
  initialization and uniqueness at every actual restart checkpoint. The 17 roots
  passed the 919-input package gate; all three restart calls are contiguous.
- [ ] Extend the created mixed ME/CS lifetimes to the remaining public
  interactions. Recurring initialization-access interleavings are now covered
  for both interfaces. Retain the numerical/source guarantee alongside every
  added public observation and the explicit caller-protocol obligations.
- [x] Derive a common actual-source-bound rejection/recovery contract for
  non-null ME state/derivative, time, entry, completion and discrete-update
  requests. Retain all modeled logging outcomes; derive observed statuses and
  callback arguments, surviving storage/owners, and source initialization at
  actual reset/entry/exit checkpoints under the universal external frame.
  The 15 roots passed the 923-input package gate. The follow-up below composes
  these into mixed histories; their creation/release composition remains open.
- [x] Compose finite admitted ME numerical/control, rejection and reset
  histories with suppressed, missing and enabled loggers. Derive raw importer
  stores, success/Error statuses, source derivative observations and every actual
  restart checkpoint, preserving all modeled callback outcomes and original
  owners. Prove actual/certified returning actions in both directions. The 15
  roots passed the 927-input package gate. These histories still start from
  typed existing instance/caller storage; the following item composes creation
  and release. Intervening initialization accesses and other public calls remain open.
- [x] Compose actual creation, initialization and mode-appropriate release
  around the mixed ME success/error/reset histories, with all modeled logger
  outcomes. Derive the handle/default/lease before the importer selects its
  history, carry original caller storage and configuration, derive actual source
  observations/checkpoints and restore the original owner map on release.
  Seven roots passed the 930-input package gate. This does not close the remaining
  public-interaction or concurrent-host obligations.
- [x] Require the complete public CS step contract in the actual artifact
  checker. All raw inputs are classified; successful/null/error/discard calls,
  exact output writes and represented logging outcomes share the prepared
  interface. Ordinary `floor`/`fegetround`, finite conversions, overflow,
  stop checks and rejection when the rounded clock cannot advance are composed.
  The strengthened contract passed the full 869-input artifact gate.
- [x] Compose initialization, finite accepted CS step histories, termination
  and atomic release from the original instance storage and lease. Derive exact
  Solve state, rounded clock/output values, source-solution error and memory
  frames without assuming later successful executions or ownership. The
  24 derived roots passed the 877-input FMI/compiler package gate.
- [x] Compose actual source-bound creation with that accepted CS lifetime.
  Available static storage supplies the handle, finite Solve default, writable
  caller/instance cells and lease. Release restores the original owner map.
  The nine added audit roots passed the 881-input FMI/compiler package gate;
  no created or initialized heap is assumed by the composed theorem.
- [x] Derive rejection→reset→reinitialization from original writable storage
  and the actual required CS call contract. Preserve the new source IVP,
  suppressed-path ownership and slot metadata. Retain all represented logging
  outcomes; recovery after a returning callback requires its explicit instance
  frame. The 16 added roots passed the 885-input FMI/compiler package gate.
- [x] Compose arbitrary finite interleavings of accepted/rejected CS steps
  and reset/reinitialization under suppressed logging. Derive all subsequent
  storage, explicit successful outputs, source epochs, numerical/clock error,
  retained control fields and atomic reservations. The 25 added roots passed
  the 890-input package gate; caller-buffer and library premises remain explicit.
- [x] Compose mixed accepted/rejected/reset histories with actual creation,
  initialization and mode-appropriate release under suppressed logging. Derive
  all later storage, source/numerical observations, the lifetime memory frame
  and restoration of the original owners. The 16 added roots passed the
  893-input FMI/compiler package gate.
- [x] Derive branching callback-enabled mixed step/reset histories from the
  actual adapter and a universal external memory frame. Retain every returning
  alternative, modeled no-return behavior, successful outputs and original
  owners; derive the source/numerical guarantee for completed actual C scripts.
  The 11 added roots passed the 896-input FMI/compiler package gate.
- [x] Compose those callback-enabled histories with actual creation,
  initialization and release for every completed actual script. Prove observed
  statuses match the reference statuses, retain every modeled callback outcome
  and restore original owners under the explicit external memory contract.
  The three added roots passed the 898-input FMI/compiler package gate. Native
  callback protocol, header and floating-environment correspondence remain
  separate obligations; FMI log callbacks must not call back into the FMU.
- [ ] Prove ME/CS trace refinement from creation through initialization,
  operation, errors, reset and release under explicit host ownership rules.
  Include preserved other-instance state and observable callback traces.

**Exit evidence:** named ME and CS refinement theorems for all admitted
histories and actual emitted functions. Finite arithmetic preservation,
continuous-solution accuracy and host/native execution remain distinct claims.

### K04 — Compose complete source, output and provenance contracts

**State:** partial; numerical, printer, literal and archive foundations exist.
**Existing IDs:** P01, C01, C02, F03, A01, PV05–PV09, eFMI E05.

- [ ] Compose every actual lowering and public observation in one driver
  theorem for all admitted source texts. Retain well-formedness, rejection,
  source-property transfer and independently specified target behaviors.
- [ ] Complete translation-unit interpretation: headers/macros, declarations,
  literal storage, function tables, linkage and modeled object layout must
  agree with the actual bytes. Symbolic-cell frames alone do not prove ABI
  layout; later machine compilation remains an external boundary.
- [ ] Bind C/GALEC/XML/ZIP members and correlated capability/value-reference
  metadata to the same source and Solve products. Preserve fail-closed,
  atomic publication and the fixed checker proposition.
- [ ] Complete required origin coverage and whole-file/archive source maps,
  including original-to-staged source identity and generated-rule ancestry.
  Keep one origin per tensor operation; preserve useful CLI/LSP error spans.

**Exit evidence:** an actual-source-to-artifact theorem containing every
mandatory lower-stage contract, complete provenance binding and the existing
artifact rejection gate. A certificate for only `model.c` cannot close this.

### K05 — Close standards, MISRA and assurance review

**State:** open; the clause/evidence ledger is authoritative.
**Existing IDs:** S01–S03, N01, C01, A02, F04, SR07–SR08, eFMI E05–E06.

- [ ] Review the frozen subset against pinned MLS 3.7, FMI 3.0.2 ME/CS and
  eFMI 1.0.0 Beta 1, using the [recurring checklist](standards-review.md#required-review-at-every-spiral-stage).
  Close the shared initialization correspondence and all applicable findings.
  Preserve SR06's documented checker limitation; do not claim an official
  checker pass or infer prose conformance from XSD validation.
- [ ] Complete the MISRA C:2025 enforcement matrix for the 223 current
  guideline entries (22 directives, 201 rules), using the supplied March 2025
  PDF pinned in the [standards review](standards-review.md#misra-c2025-and-static-storage-review).
  C11 is supported; Rule 15.5 is Disapplied, so the primary baseline requires
  no single-exit rewrite. Track withdrawn IDs. Map eFMI's MISRA AC AGC and
  C:2012 references separately; the newer book does not discharge them.
  The 223-row ledger is drafted in [misra-c-2025.md](misra-c-2025.md): every row
  stays open (four strong-partials, Rule 10.1 a deviation candidate, Rule 15.5
  Disapplied) pending independent predicates, the essential-type model and
  reviewer sign-off, so this item is not yet complete.
- [ ] For each guideline record its category, applicability/scope, independent
  predicate and proof or analyzer/manual evidence, actual-file binding, open
  finding/approved deviation and reviewer. Start formal work with Dir 4.12
  and Rule 21.3 (allocation), Rule 17.2 (recursion), Mandatory Rule 9.1
  (initialization), Rules 10.1–10.8 (essential types) and Rule 11.11 (explicit
  pointer comparisons). Preserve exact FMI time checks when resolving floating
  equality restrictions. Mandatory rules cannot be deviated.
- [ ] Include adopted FMI headers, external interfaces, compiler options,
  essential types, pointers, sequencing and concurrency. Prove the shared
  instance bookkeeping satisfies Dir 5.1–5.3 and the applicable synchronization
  rules, including sequential consistency under Rule 21.25. Document native
  RTOS timing, stack and atomic implementation assumptions separately.
- [ ] Complete MISRA Compliance:2020 and Appendix E generator documentation:
  implementation choices, essential-type strategy, runtime failure policy and
  integration interface. Keep default guideline categories unless a concrete
  recategorization plan is reviewed. Do not vendor the rulebooks or claim
  compliance from a partial policy, analyzer pass or generator exemption.
- [ ] Review theorem quantifiers, non-vacuity, all-behavior coverage and each
  premise (proved, checked, or external). Retain only `propext`, `Quot.sound`
  and `Classical.choice` in the audited roots. No placeholders, new axioms,
  native-reduction proof axioms or weakened checks. The premise and trust ledger
  drafted in [trust-ledger.md](trust-ledger.md) records the current
  classification, coverage tables and open findings; the review stays open.
- [ ] Reproduce the release in a fresh compatible workspace using normal
  trusted Lake/mathlib artifacts; record source, grammar, toolchain/options,
  checker identity, proof roots and actual outputs. Obtain independent review
  and run the final complete gate at that revision.

**Exit evidence:** resolved standards findings, complete MISRA enforcement and
compliance summary, traceable trust/coverage ledger, independent review and
passing artifact gate. DO-178C assurance remains the separate
[airborne assurance plan](airborne-assurance.md); no certification claim follows
from this checklist alone.

MISRA C:2025 §1.5.2 requires MISRA Compliance:2020; §1.5.3 and Appendix E
also govern automatic code generation. No deviations or optional guideline
recategorizations are approved. Section 1.5.4 treats the C Standard Library
separately; this does not waive the project's transitive no-allocation or RTOS
requirements. eFMI's own normative references remain explicit open work.

## Grammar expansion decision

R1 closes only when K01–K05 have their stated evidence for the whole frozen
subset. Then one small source feature may enter R2. Every new slice must ship
EBNF and source semantics, each lowering theorem, finite execution/numerical
conditions, actual FMI/eFMI artifact certificates and the recurring standards
review together. Keep the feature rejected in production until that chain is
complete. Prefer universal proofs; extend existing boundary checks only where
file I/O, native execution or protocol transport lies outside the proof model.

The required gate is:

```sh
nix develop .#verification --command lake test
```

During development use affected `lake build check-*` targets and native caching.
Never mistake `lake build audit` for the C/artifact gate or a matching hash for
semantic proof. Update this checklist after each integrated increment; keep
detailed historical logs in the existing evidence documents and Git history.

## Existing issue IDs and retained scope

IDs remain usable in commits and detailed plans. This table replaces stale
chronological “next” paragraphs; no unresolved obligation is silently closed.

| IDs | Disposition and closure requirement |
| --- | --- |
| B01–B05 | Preserved numerical/parser/artifact regression floor; not whole-FMU parity. The production parser is LALR. |
| P01a/RV02, S01a/RV03, P01b/RV04, C02a/RV06 | Earlier scoped fixes retained: frozen lowering composition, independent source semantics, property transfer and corrected duplicate-machine claims. Parent obligations remain open. |
| S01–S03 | K01/K04/K05: exact admitted semantics, independent proof review, premise and trust ledger. |
| P01 | K04: actual driver instantiates per-pass semantic/behavior contracts, including partial failure and well-formedness. |
| P02 | Closed for the authored EBNF dialect: reader soundness/completeness, EBNF→CFG and actual-source binding. It is not all ISO 14977. |
| P03–P04, LR06–LR07 | Core production cutover and located parsing checked. Retain generated child actions, richer diagnostics and generator convergence/cost work in [LALR plan](lalr-parser.md). Review the promised resource/completeness domain before admitting a larger grammar. |
| N01–N02 | K03/K05: independent IEEE/C correspondence; separate ideal Real solutions, method approximation and exact finite execution. |
| C01–C02 | K02/K04/K05: reusable C semantics, all needed call/storage rules, simulations between retained machines, complete text/profile correspondence. |
| A01–A02 | K04/K05: reproducible fixed-proposition artifact evidence and reviewed R1 release. |
| F01–F04 | K01–K05: shared ME/CS kernel, complete lifecycle/solver calls, correlated actual FMU and independent validation/release. |
| eFMI E01–E04 | Checked scoped DAE restriction, GALEC/Solve refinement, Algorithm Code and Production C contracts retained. |
| eFMI E05–E06 | K04/K05: remaining correlated artifact, initialization, coding-guideline and release obligations. These IDs belong to [efmi.md](efmi.md), distinct from performance E01–E03 below. |
| SR01–SR03, SR06 | Specific recorded corrections/disposition retained; reopen when affected. They do not close SR07/SR08 or the stage. |
| SR04 | Updated call contracts contain more evidence than the historical entry; reconcile the remaining precise finding under K03/K05. |
| SR05 | Resolved for the unit initialization admission policy by K01. SR08 and whole-interface/standards obligations remain open. |
| PV01–PV09 | Preserve checked parser/span/parallel foundations; K04 closes remaining required IR/output/actual-member provenance. [Detailed provenance ledger](provenance.md). |

## R2 — Grow the verified core in complete slices

The next authorized priority is the minimal driven/array profile and the
`jacobian` built-in, preserving tensors and proving forward/reverse AD. Complete
the existing development work in [tensor-ad.md](tensor-ad.md) before adding
unrelated grammar. Static reverse lowering, finite failure policy, prepared
metadata and actual tensor FMI/eFMI contracts remain required. Dense correctness
precedes sparse representations, whose transformations need their own proofs.

| ID | Later language work and required proof scope |
| --- | --- |
| G01 | Real constants and independent states: literal conversion, name/state mappings, initialization, permutation and duplicate/unbound-name behavior, exact rounding and numerical refinement. |
| G02 | Expressions and acyclic algebraic equations: ordered evaluation, substitution/aliases, scheduling and verified cycle rejection; no float reassociation from real algebra alone. |
| G03 | Coupled explicit ODEs: vector equations, IVP regularity, selected solver and local/global error on its stated domain. |
| G04 | A small solvable affine DAE class: elimination/matching and projection preserve solution sets; certify solvability and reject singular/inconsistent/underdetermined cases. |
| G05 | Small class/component/parameter composition: scope, renaming, instantiation and modification preserve equations. Inheritance/connectors/events need separate complete slices. |
| Q01 | Release the reusable core only with constructor-to-proof/artifact coverage, independent review, a fresh full gate and explicit exclusions. The unit corollary alone is insufficient. |

### Maintainability and efficiency

| ID | Required work |
| --- | --- |
| E01 | Measure parser/compiler memory, certificate checking and emitted C separately; establish workload and regression budgets. Keep deterministic bounded parallel parsing. Native RTOS timing/stack evidence is target-specific. [Performance audit](performance-audit.md); [OMC comparison](../docs/omc-comparison.md). |
| E02 | Enable optimizations only for measured needs, with pass proofs covering every option, signed-zero and rounding behavior. Record an empty optimization set honestly. |
| E03 | Compiler-wide identifier interning remains unimplemented. Prove collision-safe decoding, stable IDs, per-file pool merge/remapping and source/diagnostic preservation; measure memory savings. C literal pooling is not frontend interning. [Interning plan](lalr-parser.md#identifier-interning). |

## FMI 3 architecture requested during this review

Retain one prepared Solve IVP with shared model evaluation and an internal CS
solver. A CS instance does not invoke ME-only public APIs. The standard FMU
contains both ME and CS descriptions; direct RTOS use calls the shared C kernel
with supplied storage. [FMI contracts](fmi3/contracts.md) own interface details.

The compilation boundary remains Modelica → C. C → assembly, hardware/WCET,
and native ABI execution need separate evidence; do not add ARM emission to
avoid finishing the authored C contract. WASM deployment, new target plugins,
FMI 2 and broader backend/template products remain separate later work. Merge
the vetted core back into Rumoca after review and WASM deployment validation.

Design references: [IR comparison](ir-review.md), [repository ownership](../docs/layout.md),
[verification boundary](../docs/verification.md), [standards review](standards-review.md).
