# Roadmap to a verified Modelica compiler core

Reviewed **2026-09-14**. **Grammar expansion is blocked.** The numerical
source-to-C core is formally checked; complete FMI/eFMI compiler verification
is unfinished. [Verification contract](../docs/verification.md) defines the
current guarantee. This file tracks the work needed to strengthen it.

Implementation owner: Codex. Independent proof and compliance reviewers are
not yet assigned. A proof count or percentage of checked boxes is not a
percentage of semantic coverage.

## Current position

| Area | Current evidence | What remains |
| --- | --- | --- |
| Production grammar | One Modelica `Real` state with `der(state) = 1`; generic LALR engine for Modelica and GALEC. DFA implementation and generator removed in `2df35d3`. | No new source case is admitted until the closure checklist below passes. |
| Source and numerical core | Source-independent Real semantics, per-IR equation/behavior preservation, checked default initialization, binary64 rounding and the unit numerical C theorem. | Whole-interface observations and source-to-artifact composition. |
| FMI 3 ME/CS | Both interfaces share Solve. Complete CS step, termination, time and ME control-call contracts are mandatory and artifact-checked. Actual creation through an accepted CS lifetime is proved. A further actual-adapter theorem now composes creation, initialization, mixed accepted/rejected steps, repeated reset/reinitialization and mode-appropriate release with logging suppressed, retaining source/numerical guarantees, successful outputs and restoration of the original owners. Enabled-logging mixed histories also have a branching all-outcome contract and a completed-C-script source consequence under an explicit external memory frame. | Creation/release composition for enabled logging, remaining public calls, ME numerical interactions, concurrent ownership, translation-unit and ABI correspondence. |
| Initialization | Creation, entry/exit, rejection and optional logging share the actual static runtime and source IVP. The 801-input full gate and 804-input follow-up package audits passed. | Later host histories and callback frames remain in K02/K03; cross-standard correspondence remains in K05. |
| eFMI | Checked DAE → GALEC → Solve Algorithm → Production C path, method/trace proofs, correlated manifests and actual eFMU certificate. | Cross-standard initialization, coding-guideline evidence and final compliance review. |
| Tensor/AD development | Array source-to-Solve, forward derivative/reverse adjoint foundations and several prepared C contracts are checked. | These are development products; the production compiler still rejects the driven/array profiles. See [tensor plan](tensor-ad.md). |

Latest completed main-workspace gate:
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

**Distance to expansion:** K01 is closed for its scoped initialization profile;
K02–K05 remain partial or open. Actual creation now composes with the accepted
CS lifetime. Mixed accepted/rejected step and reset/reinitialization histories
now compose with actual creation, initialization and mode-appropriate release
under suppressed logging. Enabled-logging mixed histories now have a branching
contract and completed-target-script source consequence; their creation/release
composition is next. ME numerical interactions also remain open.
Concurrent storage, whole-artifact correspondence and the standards/MISRA review
remain required.
These are substantial obligations, not a final build or a parser-only change.

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

Actual CS creation now supplies the lease for initialization, accepted stepping,
termination and release, restoring the original owner map. Its derived package
gate passed on 881 inputs; the mandatory-contract full gate passed on 869.
Next, compose the remaining operation/release histories and prove actual
concurrent ownership histories. Callback frames, the transitive no-heap and
acyclic call graph, and native profile/layout remain open.
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
- [ ] Keep the RTOS kernel callable with supplied state/scratch; extend the
  existing artifact/native boundary checks for the changed storage mechanism.

**Exit evidence:** actual-function and lifetime/history theorems; certified
storage/call-graph policy in the artifact contract; both FMI interfaces and
eFMI artifacts pass the required gate. Dynamic allocator modeling is not the
next task. Any reusable storage/frame draft is only a prerequisite.

### K03 — Complete public FMI execution and histories

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
- [ ] Compose ME control histories with importer state updates, derivative
  queries and creation/initialization. Retain the numerical/source guarantee
  alongside all public observations and caller-protocol obligations.
  Initialization→controls→termination→release now has a composed actual-adapter
  theorem deriving the surviving lease from its original ownership. Actual
  creation now supplies that lease, the handle, source default and storage;
  importer state/numerical interactions still need composition.
  Reset's successful/null calls and reset→initialization composition now use
  the static object interface; arbitrary surrounding histories remain open.
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
- [ ] Compose those callback-enabled histories with actual creation,
  initialization and release. Keep every represented outcome and the external
  memory/ownership contract explicit. Native callback protocol, header and
  floating-environment correspondence remain separate obligations; FMI log
  callbacks must not call back into the FMU.
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
  native-reduction proof axioms or weakened checks.
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
