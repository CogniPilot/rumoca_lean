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
| Architecture continuity | Identify the reusable mechanism exercised by the slice, its extension point and its cost model. Small syntax coverage must use the intended compiler architecture. Grammar-specific derivations instantiate general parser/lowering theorems; fixed examples or temporary recognizers cannot replace them. |
| Normative baseline | MLS, FMI and eFMI versions; relevant clauses; pinned header/schema identities. Upstream Rumoca and compliance tools are references, not normative authorities. |
| MLS coverage | Lexical/syntactic admission, resolution, types and shapes, equation meaning, initialization, numeric interpretation and diagnostics. Keep `jacobian` explicitly identified as an extension. |
| FMI coverage | Both advertised ME and CS interfaces: metadata, initialization, legal and rejected calls, time/solver policy, errors/logging, storage/lifetime, source builds and archive contents. |
| eFMI coverage | GALEC semantics and methods, sample-period policy, Production C execution, logical mappings/status, correlated manifests/checksums, archive layout and coding-guideline obligations. |
| Proof correspondence | For each applicable clause: independent specification, lowering/target theorem roots, actual-file/archive proposition and any remaining external assumptions. Inspect elaborated quantifiers and interface instances for accidental specialization to imported constants; an axiom audit does not establish the intended scope. A theorem about an emitter's own policy does not establish that policy's conformance. |
| Boundary evidence | Required `lake test` outcome and artifact identities, plus existing schema/importer/native checks where tools or interfaces lie outside Lean. Record checker limitations explicitly. |
| Decision | Carry forward every open finding with closure criteria. Close applicable findings before growth. Record a reason for each excluded clause; an unproved advertised behavior cannot be marked inapplicable. |

The stage is **open** if any applicable compliance finding or required compiler
proof/artifact obligation remains unresolved. A passing schema, importer or CI
run cannot change that decision by itself. This is a review gate, not an
automated claim that Lean has formalized the prose standards. Use universal
proofs for compiler properties and keep tests to the existing external boundaries.

## Current unit-stage follow-up

### Created ME numerical lifetime: 2026-09-14

This derived follow-up to `bc19ec0` connects actual creation, initialization,
accepted mixed control/state/derivative histories, termination and release in
one header/object/literal environment. Creation establishes the handle, source
default and lease before the importer chooses its history. Caller storage is
specified before creation; later writable cells, metadata and owners are
derived. Release restores the original owners and preserves unrelated memory.

The focused review rechecked pinned FMI 3.0.2
[§2.3.3](https://fmi-standard.org/docs/3.0.2/#state-initialization-mode),
[§2.3.4](https://fmi-standard.org/docs/3.0.2/#super-state-initialized) and the
[instance lifetime functions](https://fmi-standard.org/docs/3.0.2/#state-machine).
ME initialization exits into Event Mode; the admitted history preserves a mode
from which termination is allowed, then releases its instance. This result
does not close the full resource/native lifetime obligation or arbitrary
reset histories. Existing single-call failure and logging contracts remain.

`runtime_create_me_numerical_release` retains source compilation, numerical C,
function-section tokenization and derivative/state metadata. It derives actual
statuses and raw query values without assuming expected observations. Source
initialization is recorded at the initialized heap, before importer trial-state
updates; derivative queries retain source Real equation agreement. The result
does not certify an importer's integration method or native external code.

All eleven added roots passed the FMI/compiler package gate on 914 unchanged
inputs in `build/c-factory/me-numerical-lifecycle-package-v1.log`. Only the three
status documents changed afterward. Earlier semantics, emission, mandatory
contracts and tests retain the separate 869-input full gate and unchanged
archives; their source and archive hashes were rechecked. MLS 3.7, CS/eFMI and
MISRA clause records carry forward unchanged. No grammar feature, new test suite,
full-gate pass or standards closure is claimed. Mixed ME rejection/reset/callback
histories, remaining public calls, concurrency and complete artifact/native
correspondence keep K02–K05 and grammar expansion open and blocked, respectively.

### Mixed ME control and numerical histories: 2026-09-14

This derived follow-up to `ac3b5b5` uses one actual function table/pool for
controls, continuous-state access and derivative queries. The history derives
typed importer buffer writes, subsequent storage, control outputs and read-only
diagnostic preservation. The actual execution relation records arbitrary
statuses, events and raw query values; expected control flags and finite/correct
query results occur only in the derived certificate and its consequences.

The focused review rechecked pinned FMI 3.0.2
[§3.2.1](https://fmi-standard.org/docs/3.0.2/#state-continuous-time-mode) for
time/state updates, ordered state/derivative access and integrator completion,
and retains the [§2.3.5](https://fmi-standard.org/docs/3.0.2/#state-event-mode)
event-iteration and [§2.4.8](https://fmi-standard.org/docs/3.0.2/#model-structure)
metadata records. Setters supply trial states; queries describe the prepared
equations. The proof does not certify the importer's integration algorithm or
identify arbitrary trial states with the source IVP solution. The unit RHS
remains finite and independent of time/state; existing failure policy is unchanged.

`runtime_me_numerical_history` binds source compilation, numerical C, function
tokenization and derivative/state metadata to the history. Observed statuses,
raw query results and final memory are derived for every completed actual script;
every derivative result corresponds to the source Real equation. Complete
single-call failures/logging remain in the prepared contracts. Initial typed
instance storage, a separate reusable float buffer and the control output bank
remain premises. Creation/reset/rejection/release composition, external callback
frames and native ABI/header correspondence remain open.

All 24 roots passed the FMI/compiler package gate on 910 unchanged inputs in
`build/c-factory/me-numerical-history-package-v1.log`. Only the three status
documents changed afterward. Earlier semantics, emission, mandatory contracts
and tests retain the separate 869-input full gate and unchanged archives;
their source hashes and retained archive hashes were rechecked. MLS 3.7 source
and initialization policy, CS/eFMI execution and generated C/GALEC/XML are
unchanged. Their clause records and all MISRA findings carry forward. No new
full-gate pass, grammar feature, test suite or conformance closure is claimed.
K02–K05 and the grammar gate remain open.

### ME control runtime bridge: 2026-09-14

This derived follow-up to `fedf3dd` transports the existing ME control contracts
to the explicit header/object/literal interface. The reviewed policy and actual
function bodies are unchanged. Reuse the clause/evidence records under
"Mandatory ME control histories" and "ME derivative queries and source
equations" below. MLS 3.7, FMI 3.0.2, eFMI Beta 1 and MISRA C:2025 findings
carry forward; no standard or initialization policy is reinterpreted here.

Successful/null event entry, continuous entry, completion and discrete update,
their rejected calls, and time rejection retain the existing contracts.
Suppressed logging includes absent loggers. Enabled callbacks retain every
modeled returning outcome and the no-return alternative, with immutable
diagnostics. Native callback behavior, ABI/header correspondence, caller storage
and ownership remain explicit boundaries. These individual calls do not prove
mixed importer state/control/derivative histories or a source IVP trajectory.

All 21 added roots passed the FMI/compiler package gate on 904 unchanged inputs
in `build/c-factory/me-controls-environment-package-v1.log`. Only the three
status documents changed afterward. Earlier semantics, emitters, mandatory
contracts and tests retain the separate 869-input full gate and archives;
their source hashes and both retained archive hashes were rechecked. No new
full-gate pass, source feature, test suite or compliance closure is claimed.
Prepared-pool and numerical-history composition remain next. K02–K05 and
the grammar gate remain open.

### ME derivative queries and source equations: 2026-09-14

This derived follow-up to `896ed51` supplies state-access and derivative-access
contracts from one actual function table and literal pool. The public derivative
getter follows the existing guard, actual `model_rhs`, numerical C kernel,
output write and status return in the header/object/literal runtime used by
creation and CS. The compiler consequence retains actual source compilation,
numerical C and derivative/state metadata, and derives exact finite Solve
agreement and the source Real equation through the existing IR theorems.

Applicable pinned FMI 3.0.2 clauses remain
[§2.3.3](https://fmi-standard.org/docs/3.0.2/#state-initialization-mode),
[§2.3.5](https://fmi-standard.org/docs/3.0.2/#state-event-mode),
[§2.3.8](https://fmi-standard.org/docs/3.0.2/#state-terminated),
[§3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3GetContinuousStateDerivatives), and
[§2.4.8](https://fmi-standard.org/docs/3.0.2/#model-structure).
The immediately preceding focused review and the earlier derivative/state
clause records are reused for unchanged policy. The getter returns the ordered
continuous-state derivative; it does not advance a solver. The admitted unit
RHS is finite and state independent, so no numerical failure branch is added.
The bracketed Discard advice is not claimed as a generalized failure policy.
Retrieval following Error remains diagnostic, and arbitrary importer trial
states are not identified with a solution of the original IVP.

Null and both independently classified rejection reasons retain their existing
complete calls. Logging suppression covers a disabled flag or missing callback;
enabled logging retains every modeled returning effect and the no-return case.
Diagnostics on later heaps require the established read-only pool frame.
Native callbacks, caller storage/ownership and header/ABI correspondence remain
explicit boundaries. These call proofs do not close mixed ME histories.

The shared helper proof reuses the existing numerical scheduler with explicit
type and symbol bindings. No new source resolution, solver selection, shape
inference, scalarization or DAE work enters the backend. Production grammar,
source/initialization semantics, emitted C/GALEC/XML and archive behavior are
unchanged. The pinned MLS/eFMI/MISRA baselines and open findings carry forward.

The eleven new roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-derivative-environment-package-v1.log` on 903 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full gate and
archives in `build/c-factory/cs-contract-artifacts-v1/`. No new test suite or
full-gate pass is claimed. **Stage decision: open; no grammar expansion.**

### ME state access in the shared runtime: 2026-09-14

This derived follow-up to `a8e4d95` connects the existing complete state-access
contracts to the same header/object/literal interface used by actual creation
and lifecycle calls. The actual source-bound accessor fragments and pool are
retained. Arbitrary later heaps may be used: valid typed caller/instance storage
is explicit, and failures require the read-only diagnostic pool to survive.
Suppression covers both a disabled flag and a missing callback. Enabled logging
retains every modeled returning effect and its no-return alternative.

The focused review rechecked FMI 3.0.2
[§2.3.3](https://fmi-standard.org/docs/3.0.2/#state-initialization-mode),
[§2.3.5](https://fmi-standard.org/docs/3.0.2/#state-event-mode),
[§2.3.8](https://fmi-standard.org/docs/3.0.2/#state-terminated), and
[§3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3SetContinuousStates).
The ME getter remains available in Initialization, Event, Continuous-Time and
Terminated modes; the setter supplies new states in Continuous-Time mode.
State ordering retains the existing XML/state metadata contract. A trial-state
setter copies the supplied value; it does not integrate or establish accuracy
of the importer's trajectory. Final retrieval after Error remains diagnostic.
The earlier finite-Real/fail-stop policy and its Error-versus-Discard review are
unchanged; this increment does not attribute that policy to new standard text.

Shared body-interface and complete failure-helper proofs are reused. No source
resolution, shape inference, scalarization, solver selection or DAE work is added
to the backend. Grammar, source/initialization semantics, emitted C, GALEC, XML
and packaging are unchanged. The pinned MLS/eFMI/MISRA baselines and all open
findings carry forward; native callback/ABI and concurrent-host obligations
remain separate. Complete ME state/derivative/control histories are still open.

All six added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-state-environment-package-v1.log` on 900 unchanged inputs.
Only the three status documents changed afterward. The unchanged earlier
semantics, emission, mandatory contracts and tests retain the separate 869-input
full gate and archives in `build/c-factory/cs-contract-artifacts-v1/`.
No new test suite or full-gate pass is claimed.
**Stage decision: open; no grammar expansion.**

### Created callback-enabled CS lifetime and observed statuses: 2026-09-14

This derived follow-up to `0afdea3` connects the actual factory and initialization
to callback-enabled mixed step/rejection/reset histories. Original available
storage supplies all created-state and lease premises. The branching contract
retains every modeled outcome; for every completed actual C script, its status
list is proved equal to the reference list and its source/numerical observation
and release ownership are derived. Termination/free follows the final mode and
restores the original owner map. Protected unrelated instance/reservation cells
are retained; private logger storage is allowed to change.

The prior focused FMI 3.0.2 review is reused for unchanged policy:
[§2.2.1, callback protocol](https://fmi-standard.org/docs/3.0.2/#requirements-for-implementations-of-the-c-api),
[§2.2.4, statuses](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
and [§2.3.1, creation/reset/release](https://fmi-standard.org/docs/3.0.2/#super-state-fmu-state-settable).
Expected statuses are now conclusions for completed histories rather than
premises. The universal external memory frame and existing returning-effect
model remain explicit; this does not prove native callback behavior or permit
log callback reentry. No callback return or eventual release is presumed for a
blocked history. No logging/category, source initialization or emitted policy
changed. Existing broader single-call contracts remain intact.

The FMI/compiler package gate passed in
`build/c-factory/cs-logged-lifetime-package-v1.log` with all 898 inputs unchanged
and three added roots. Only the three status documents changed afterward.
Earlier semantics, emission, mandatory contracts and tests retain the separate
869-input full gate and archives in `build/c-factory/cs-contract-artifacts-v1/`.
No new full-gate pass or example suite is claimed. The pinned MLS/eFMI/MISRA
baselines and findings remain open where previously open. Remaining public/ME
interactions, concurrency, artifact/native correspondence and the final standards
review are still required. **Stage decision: open; no grammar expansion.**

### Callback-enabled mixed CS histories: 2026-09-14

This derived follow-up to `938987a` proves branching accepted/rejected step and
reset/reinitialization histories using the actual prepared adapter. Complete
call alternatives preserve callback symbols/arguments and all returning effects;
a callback with no modeled return retains the existing `wrong` alternative.
Every returned branch derives later storage, successful outputs and ownership.
An independently defined completed C-call script retains the final source IVP
and numerical/clock error bound. No successful callback is an initial premise.

Applicable FMI 3.0.2 clauses are
[§2.2.1, C-API requirements](https://fmi-standard.org/docs/3.0.2/#requirements-for-implementations-of-the-c-api),
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
and [§2.3.1, logging and reset](https://fmi-standard.org/docs/3.0.2/#super-state-fmu-state-settable).
The actual callback invocation retains the environment, status, category and
message arguments. The universal external frame protects the instance pool,
reservation block and caller outputs, while allowing private logger effects.
It is an integration contract, not a consequence of the FMI prose alone.
FMI prohibits log callbacks from calling back into the FMU; supporting such
reentry is not a new admitted requirement. Native protocol conformance,
divergence and floating-environment correspondence remain explicit boundaries.
Disabled/missing-logger histories and the broader single-call contracts remain
unchanged; no logging/category policy or metadata changed.

The FMI/compiler package gate passed in
`build/c-factory/cs-run-logging-package-v1.log` with 896 unchanged inputs and
11 added roots. Only the three status documents changed afterward. Earlier
semantics, emission, mandatory contracts and tests retain their separate
869-input full artifact gate and archives under
`build/c-factory/cs-contract-artifacts-v1/`; no new full-gate pass is claimed.
MLS/eFMI/MISRA findings remain unchanged. Creation/release composition for the
enabled-logging trace, remaining APIs, ME numerical histories and concurrency
still require work. **Stage decision: open; no grammar expansion.**

### Created mixed CS lifetime with logging suppressed: 2026-09-14

This derived follow-up to `eb0d3a0` connects actual creation and initialization
to mixed CS steps/rejections/reset histories and final release. It derives the
selected handle and all later storage from available initial storage, preserves
successful outputs and the source/numerical invariant, and restores the original
owner map. The ordinary frame covers the complete lifetime outside the selected
instance, caller outputs and released reservation flag.

The focused review uses FMI 3.0.2
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
[§2.3.1, reset and release](https://fmi-standard.org/docs/3.0.2/#super-state-fmu-state-settable),
and [§2.3.8, Terminated](https://fmi-standard.org/docs/3.0.2/#state-terminated).
The final Step path calls Terminate before FreeInstance; a path already
Terminated by an error calls FreeInstance directly. Reset restores defaults and
initialization establishes the new run. Preserved stored values after an error
do not authorize continued simulation; this result adds no getter-call claim.
The existing broader single-call logging contracts remain intact.

All 16 added roots passed the FMI/compiler package gate in
`build/c-factory/cs-run-lifecycle-package-v1.log`, with 893 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics,
emission, mandatory contracts and tests are unchanged, retaining the separate
869-input full gate and archives in `build/c-factory/cs-contract-artifacts-v1/`.
No new full-gate pass or example suite is claimed. This theorem assumes
suppressed logging, the explicit nearest-rounding/library profile and the
existing typed caller-buffer bank; callback effects and concurrent histories
remain open. Existing MLS/eFMI/MISRA findings are carried forward, not closed by
this scoped review. **Stage decision: open; no grammar expansion.**

### Mixed CS steps and recovery with logging suppressed: 2026-09-14

This derived-proof follow-up to `4d0d79e` adds 25 audit roots. An independent
reference relation tracks lifecycle mode, source initial value/time origin,
rounded communication time and cumulative solver duration within each run.
The actual-adapter theorem composes finite accepted/rejected step histories
and repeated reset/reinitialization. It derives later writable state/caller
storage, retains all four successful step outputs and preserves read-only
diagnostics, logger configuration, slot metadata and atomic reservations.
Each stored sample retains the source IVP and numerical/clock error bound.

Applicable FMI 3.0.2 clauses remain
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
[§2.3.1, reset](https://fmi-standard.org/docs/3.0.2/#fmi3Reset) and
[§4.2.1, Step Mode](https://fmi-standard.org/docs/3.0.2/#step-mode).
The observation relation specifies successful outputs explicitly. Error and
discard outputs have no standards-level value requirement; reset restores
defaults before reinitialization. Review strengthened the initial history draft
to make successful outputs explicit before accepting this checkpoint.
No emitted behavior, capability or admission policy changed.

The final package gate passed in `build/c-factory/cs-run-package-v2.log` with
all 890 inputs unchanged. Only the three status documents changed afterward.
The earlier 869-input full gate and retained archives under
`build/c-factory/cs-contract-artifacts-v1/` remain evidence for unchanged
semantics, emission, mandatory contracts and existing tests. No new full-gate
pass or test suite is claimed for this derived increment.

This trace uses suppressed logging, an explicit nearest-rounding library
profile and a fixed typed output-buffer bank or omitted pointers. The broader
single-call contracts are retained. Callback-enabled mixed histories,
creation/release composition, ME numerical interactions, concurrency and native
profile/layout remain open. Existing MLS/eFMI/MISRA findings and pinned baselines
are carried forward; this scoped FMI follow-up is not a repeated full review.
**Stage decision: open; no grammar expansion.**

### CS rejection, reset and reinitialization: 2026-09-14

This derived-proof follow-up to `d331349` adds 16 audit roots. The actual
required CS rejection contract now composes with reset and both initialization
calls in one header/object/literal environment. Original writable storage
supplies the later storage; the result retains the Solve default and a new
source IVP at the requested start time. Suppressed logging preserves atomic
reservations, original ownership and slot metadata. Enabled logging retains
all modeled outcomes; each returning callback permits the recovery consequence
only if it preserves the instance record. Global callback lease frames and
reentry are not discharged by that premise.

Applicable clauses are FMI 3.0.2
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions)
and [§2.3.1, reset](https://fmi-standard.org/docs/3.0.2/#fmi3Reset).
Error permits recovery by reset; discard preserves the FMU state. Reset restores
defaults and requires initialization before another run. The new proofs
strengthen correspondence for these existing policies. They change no emitted
transition, logging policy, source admission, capability or initialization
choice, and do not close whole-standard correspondence.

The FMI/compiler package gate passed in
`build/c-factory/cs-recovery-package-v1.log` with all 885 inputs unchanged.
Only the three status documents changed after acceptance. Earlier semantics,
emission, mandatory contracts and existing tests are unchanged; the 869-input
full gate and archives under `build/c-factory/cs-contract-artifacts-v1/` retain
their original scope. No new full-gate pass or test suite is claimed.

The pinned MLS/eFMI/MISRA baselines and findings remain open where previously
open; this is a scoped FMI recovery follow-up, not a repeated full review.
Complete mixed simulation histories, ME numerical interactions, callbacks,
concurrent ownership, native profile/layout, cross-standard initialization and
coding-guideline correspondence still block expansion. **Stage decision: open.**

### Actual creation through accepted CS lifetime: 2026-09-14

This derived-proof follow-up to `0979ebd` adds nine audit roots. The actual
CS factory, source identity validation, initialization, accepted numerical
history, termination and release now share one prepared program and explicit
header/object/literal interface. Available static storage supplies the handle,
finite Solve default, writable state/caller cells and lease. Release restores
the original owner map. The initialized source solution, numerical/clock error,
bounded reservation trace and memory frames are retained. The former
initialized-lifetime theorem keeps its statement and reuses the shared backend
composition. No created or initialized heap is an input premise.

The FMI/compiler package gate passed in
`build/c-factory/cs-created-lifetime-package-v1.log` with all 881 inputs
unchanged. Only the three status documents changed after acceptance. Earlier
semantic definitions, emitted products, mandatory artifact contracts and
existing tests are unchanged; the preceding 869-input full gate and archives
under `build/c-factory/cs-contract-artifacts-v1/` remain their evidence. No new
full-gate pass or test suite is claimed.

This strengthens the proof correspondence for the already reviewed FMI
instantiation, initialization, Step Mode, termination and release profile.
It changes no admission policy, capability or emitted lifecycle transition.
The pinned baselines and existing MLS/FMI/eFMI/MISRA findings are retained.
Mixed error/discard/logging/reset histories, ME numerical interactions,
callback effects/reentry, concurrent ownership, native header/layout and
cross-standard initialization/coding-guideline correspondence remain open.
Neither this composed theorem nor the earlier artifact checks establish
whole-standard conformance. **Stage decision: open; no grammar expansion.**

### Mandatory CS calls and initialized CS lifetimes: 2026-09-14

This increment follows `9f85945`. Eighteen added roots make the complete CS
step-call contract mandatory for actual adapter certification. It covers all
eight raw admission cases and suppressed/supplied logging in the prepared
static interface. The required full artifact gate passed in
`build/c-factory/cs-contract-full-gate-v1.log`, with all 869 inputs unchanged.
The retained FMU/eFMU and comparisons are under
`build/c-factory/cs-contract-artifacts-v1/`. All FMU member contents match the
preceding artifacts; the eFMU differs only in three manifests' fresh generation
identities and dependent references/checksums. The existing archive, importer,
native C and rejection checks passed. No new test suite was introduced.

Twenty-four further derived roots compose actual initialization, any finite
accepted CS request sequence, termination and release from original instance
storage and ownership. The source consequence retains the initialized Real
solution, exact finite Solve state, rounded communication clock and separate
numerical/clock error terms. The FMI/compiler package audit passed in
`build/c-factory/cs-history-package-v1.log`, with all 877 inputs unchanged.
The mandatory contracts, earlier semantics and emission are unchanged by this
follow-up; its package evidence is distinct from the retained 869-input full
artifact gate. Only the three status documents changed after package acceptance.

Applicable pinned clauses are
[FMI 3.0.2 §2.2.6](https://fmi-standard.org/docs/3.0.2/#advancing-time),
[initialization](https://fmi-standard.org/docs/3.0.2/#fmi3EnterInitializationMode),
[§4.2.1, `fmi3DoStep`](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep), and
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions).
The accepted reference starts at the initialization time and requires positive
admitted durations, a progressing reported clock and the optional stop bound.
Keeping solver duration distinct from reported time accommodates the specified
possibility of a reported time differing from the requested endpoint. Error
and Discard output values remain implementation evidence, not importer promises.
The logged single-call contract retains all modeled callback outcomes; the
accepted sequential lifetime has no interspersed logging or rejected calls.

This is a scoped follow-up, not a new complete MLS/eFMI/MISRA review. Source
grammar and emitted products are unchanged. Creation composed with the CS
lifetime, mixed error/reset histories, callback frames/reentry, concurrent
ownership, native headers/layout and existing MLS/eFMI initialization and
coding-guideline findings remain open. The formal call contract establishes
the authored execution model; it does not by itself establish native ABI or
whole-standard correspondence. **Stage decision: open; no grammar expansion.**

### Complete CS discard calls and raw-input partition: 2026-09-14

This derived-proof increment follows `f1113bb`. Sixteen added roots cover
complete public discard calls and exhaustive, disjoint raw-input admission.
The core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/cs-cases-package-v1.log` with all 863 inputs unchanged. The
preceding discard-only package audit passed with 861 unchanged inputs. Only
three status documents changed afterward. Earlier declarations, emission,
mandatory artifact contracts and tests are unchanged; the preceding 855-input
full artifact gate remains their evidence. No new full-gate pass is claimed.

[FMI 3.0.2, `fmi3DoStep`](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep)
permits Discard with the FMU's previous state retained and leaves the output
arguments undefined. The checked implementation initializes those arguments
while preserving all instance cells before any logger call. Suppressed logging
therefore returns Discard with the prior instance intact. The logged theorem
represents every foreign callback outcome; deriving the same preservation
after logging requires the external callback's frame. It does not verify native
callback internals or reentry. Both discard paths follow the stop check, and
neither invokes the solver. No numerical-progress or output-value promise is
assigned to an importer after Discard.

Raw admission covers all bit patterns and preserves signed-zero encodings.
This supplies a coverage prerequisite for the mandatory public-CS contract;
it does not independently establish the policy's conformance. That contract,
repeated histories, shared initialization, native header/ABI correspondence and
existing MLS/eFMI/MISRA findings remain open. **Stage decision: open; no grammar
expansion.**

### Complete CS rounding and stop-limit errors: 2026-09-13

This derived-proof increment follows `095323c`. Eleven new roots compose
public output/input admission, ordinary rounding observations and stop-limit
rejection with the actual error helper. Suppressed logging and every represented
callback outcome are retained. The core/C/FMI/eFMI/compiler package audit passed
in `build/c-factory/cs-failures-package-v1.log` with all 860 inputs unchanged;
only three status documents changed afterward. Every earlier declaration,
emitter, mandatory contract and test is retained. The preceding 855-input full
artifact evidence still applies; the full gate was not rerun for this increment.

[FMI 3.0.2, `fmi3EnterInitializationMode`](https://fmi-standard.org/docs/3.0.2/#fmi3EnterInitializationMode)
requires Error when the importer attempts to compute beyond a defined stop
value. The new stop-call theorem includes the rounded binary64 sum and overflow,
and preserves the stop check before discard checks. The rounding-call theorem
uses the explicit header and ordinary-library profile already recorded below;
it does not certify the native floating environment, flags or traps.
[§2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions) governs
Error and logging. The proof retains exact implementation output writes while
keeping Error outputs undefined to an importer. Native callback execution,
reentry and instance isolation still need integration evidence. The new public
calls are not yet mandatory in the actual-adapter certificate. Discard and
repeated histories remain open; existing MLS/eFMI initialization, coding-guideline,
MISRA and native-header/ABI findings are unchanged. **Stage decision: open;
no grammar expansion.**

### Complete CS argument-error calls: 2026-09-13

This proof-only increment follows `a5967dd`. Twelve added roots cover the
complete missing-output and raw-numerical-input rejection calls, including
suppressed logging and every represented callback outcome. Shared direct-prefix
bridges also simplify existing error/lifecycle proofs without changing their
propositions. The FMI/compiler package audit passed in
`build/c-factory/cs-arguments-package-v1.log` with all 859 inputs unchanged;
only three status documents changed afterward. Emission, earlier semantics,
mandatory contracts and tests retain the preceding 855-input full artifact
evidence; the full gate was not rerun for these derived proofs.

[FMI 3.0.2 §2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions)
requires Error when illegal arguments are detected and leaves returned output
arguments undefined on Error. The proofs retain the implementation's exact
output writes without turning those values into an importer guarantee. Missing
pointers cause rejection before output access; invalid numerical inputs cause
rejection after output initialization. [§4.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep)
defines the communication-point and positive-step arguments. All raw encodings
are covered by the existing finite-value admission predicate. Writable caller
storage remains explicit, and enabled callbacks retain their modeled effects;
native validity, reentry and other-instance isolation still need integration
evidence. The mandatory CS artifact contract and rounding/stop/discard/history
proofs remain open. Existing MLS/eFMI initialization, coding-guideline, MISRA
and native-header/ABI findings are unchanged. **Stage decision: open; no grammar
expansion.**

### Explicit error contexts and complete CS lifecycle rejection: 2026-09-13

This proof increment follows `0d4fe05`. Checked local interface requirements
allow the existing error-helper proofs to serve both static objects and an
explicit rounding header. Fourteen existing roots are generalized; sixteen
caller sites retain their public contract statements. Eleven added roots
include complete CS lifecycle rejection with enabled/suppressed logging and
all represented foreign outcomes. The FMI/compiler package audit passed in
`build/c-factory/cs-errors-package-v1.log` with all 858 inputs unchanged; only
three status documents changed afterward. Emitters, earlier semantics,
mandatory artifact contracts and tests remain unchanged, retaining the
preceding 855-input full-gate artifact evidence.

[FMI 3.0.2 §2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions)
requires Error for forbidden lifecycle calls and respects logging settings;
[§2.3.1](https://fmi-standard.org/docs/3.0.2/#FMUStateSettable) routes Error to
Terminated. The new call proofs derive the actual mode write and Error return
for the represented forbidden kinds/modes. Output storage is unnecessary:
rejection precedes every output access. Enabled logging retains the represented
callback's effects and traces; it does not certify native callback execution,
reentry or cross-instance ownership. Those assumptions need the remaining
history and integration evidence.

The public CS results are not yet mandatory in the actual-adapter certificate.
Other argument/rounding/stop/discard paths and repeated histories remain open.
Existing MLS/eFMI initialization, coding-guideline, MISRA and native-header/ABI
findings are unchanged. **Stage decision: open; no grammar expansion.**

### Public CS entry and raw-input classification: 2026-09-13

This derived-proof increment follows `8ac1292`. Sixteen new `StepEntry` roots
cover typed public arguments, every raw point/step input encoding, lifecycle
and output setup, complete successful/null calls, output values and memory
frames. They passed the FMI/compiler package audit in
`build/c-factory/cs-entry-package-v1.log` with all 856 inputs unchanged; only
three status documents changed afterward. Earlier semantics, emitters and
mandatory artifact contracts are unchanged, retaining the preceding full-gate
artifact evidence. No grammar or new test suite is introduced.

[FMI 3.0.2 §4.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep) defines
positive communication steps and the returned time and event/termination
outputs. The new proof derives the rounded returned time and false output
flags for the current event-free unit profile. The guard compares finite
numerical point/clock values, including both signed zeros. It reaches the
actual rejection statement for invalid raw inputs after the existing output
initialization. The remaining failure/logging and discard-state-restoration
proofs are still required; this increment does not establish them.

The complete success theorem uses an explicit typed-memory and external-library
profile. Native headers/ABI, floating flags/traps, surrounding callback behavior
and repeated clock/source histories remain outside this result. The new public
call theorem is not yet required by the actual-adapter certificate. Existing
MLS/eFMI initialization, coding-guideline and MISRA findings are unchanged.
**Stage decision: open; no grammar expansion.**

### Ordinary CS calls and guarded numerical execution: 2026-09-13

This increment follows `aa5ef00` and changes the emitted CS body. Rounding
and floor calls now initialize explicit function-scope locals. The guard
destination proofs cover all supplied int32 rounding observations and every
finite clock/duration operand, including overflowing sums. The successful
suffix theorem derives its solver count and exact final writes. Eight new
audit roots passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-ordinary-package-v1.log`, with all 855 inputs unchanged.
The renewed full artifact gate passed in
`build/c-factory/cs-ordinary-full-gate-v1.log`, with the same 855 inputs
unchanged and all 13 existing native FMI checks passing. Both archives and
exact member comparisons are retained under
`build/c-factory/cs-ordinary-artifacts-v1/`. The FMI adapter source and binary
changed; numerical C, headers, FMI metadata, GALEC and eFMI Production C are
unchanged. The eFMI manifests differ only in fresh generation identities and
dependent checksums. Only the three status documents changed after the gate.
No grammar or Solve policy change is made.

[C11 §6.5.13–14](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
requires short-circuit evaluation: the normalization keeps floor after the
finite/progress checks and keeps the optional stop rejection before discard.
The earlier header/floor reviews still apply. The theorem describes the new
actual statement sequence; no semantic equivalence to an unsupported nested
ordinary-call expression is assumed. Native control/flags, header/library
correspondence and excess-precision behavior remain separate obligations.

[FMI 3.0.2 §4.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep) requires a
positive communication step and defines the requested next communication
point. The suffix proof retains the finite rounded communication clock and
separate unit-grid count. It does not yet compose public output initialization,
input/lifecycle rejection, all status/logging outcomes or repeated-step
histories. Existing MLS/eFMI initialization and MISRA findings are unchanged.
**Stage decision: open; no grammar expansion.**

### Explicit rounding header and shared execution environment: 2026-09-13

This derived-proof increment follows `3818eec`. Fourteen C/FMI/compiler roots
supply a header-parametric rounding binding, the ordinary observation/branch
prefix, reusable local body-call transfer, and actual-adapter consequences for
ME quiet-time calls, their history/source frame and the numerical helper.
The same definition table and literal pool serve every header value. The
core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/rounding-environment-package-gate-v1.log`, with all 854 inputs
unchanged. Only the three status documents changed afterward; the full gate
was not rerun for these derived proofs, retaining the preceding 847-input
full artifact evidence. Existing definitions, emitters and mandatory artifact
contracts remain unchanged; no new source case is admitted.

[C11 §7.6 paragraph 8 and §7.6.3.1](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
require distinct nonnegative supported rounding-direction macro values and
allow a negative `fegetround` failure result. The proof header selects the
existing int32 target profile and supplies a bounded value explicitly; it does
not assume that the macro is zero. Negative observations cannot equal this
nearest-mode value. Reading/validating the native header and relating the
ordinary external binding to the native environment remain separate work.

The value-only guard theorem does not establish mode stability, floating flags,
traps or restoration required by the applicable C/FMI environment contract.
It describes the proposed ordinary-call form; generated `doStep` still uses
nested calls, so actual guarded-body integration remains open. ME errors and
complete histories still need transfer to the extended environment. No MLS,
eFMI or MISRA finding is closed. **Stage decision: open; no grammar expansion.**

### CS duration and ordinary call continuations: 2026-09-13

This derived-proof increment follows `d80cdce`. Fourteen shared C/FMI roots
connect ordinary floor/rounding calls to fresh local declarations, mathematical
duration admission to the actual comparisons and bounded solver count, and the
actual solver/time/output suffix to its nested execution and memory frame.
The C count conversion is derived from exact duration. An admitted duration
implies finite clock addition, while the separate progress guard remains
necessary. The core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/cs-duration-package-gate-v2.log` with all 850 inputs unchanged.
Only the three status documents changed afterward; the full gate was not
rerun for these derived proofs.

The existing C11 cast, floor and rounding-observation review applies. Neither
these proofs nor the unchanged prior artifact gate establish target-header
bindings, floating-environment correspondence or a complete public CS call.
Initial output setup, every rejection/logging path and repeated-step histories
remain open. No MLS/eFMI syntax, initialization, solver policy or emitted member
changes; the preceding 847-input full gate supplies unchanged artifact evidence.
No standards or MISRA finding is closed. **Stage decision: open.**

### Finite-operand addition overflow: 2026-09-13

This checkpoint follows `5c06e00`. Shared C addition now represents overflow
from two finite operands as signed infinity. The independent Real result
relation retains strict finite bounds, nearest/even rounding and signed zero;
its two threshold ties overflow. Encoding/decoding, result correspondence,
infinity classification/comparison and member/register expression proofs add
21 audit roots. Earlier finite theorem statements and mandatory contracts are
retained. The core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/finite-addition-package-gate-v1.log` with all 847 inputs
unchanged. The renewed full artifact gate passed in
`build/c-factory/finite-addition-full-gate-v1.log`, also with all 847 inputs
unchanged. Both checked archives are retained under
`build/c-factory/finite-addition-artifacts-v1/`; exact comparisons preserve
C/header/GALEC and FMI XML bytes, permitting only fresh eFMI manifest identities
and their dependent checksums. The existing native FMI check passed
overflowing calls with and without a stop bound. Only the three status
documents changed after full acceptance.

The result model follows the current nearest-even binary64 profile and the
[C11 Annex F.3](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
mapping of addition to IEC 60559. Annex F.8.6/F.9.1 also requires attention to
floating status flags and control modes; these are outside this numerical
result relation. Native compiler/environment correspondence remains an
explicit review obligation. A result-bit theorem is not a proof of the
complete floating environment or all ISO C implementations.

[FMI 3.0.2 §2.2.1](https://fmi-standard.org/docs/3.0.2/#general-mechanisms)
requires restoration of changed thread settings before return or callbacks.
Retain the environment correspondence/restoration obligation in K03/K05;
distinguish operation status flags from control-setting changes during that
review. No restoration guarantee follows from the new value-only theorem.
Generated `fmi3DoStep` still adds before checking the step cap and keeps its
existing stop-error/discard ordering. The complete public proof must connect
the new overflow result to those actual guards, callbacks and output writes.

No MLS 3.7/eFMI Beta 1 syntax, initialization, lowering, solver policy or
generated member changes. No MISRA, FMI or other standards finding is closed.
**Stage decision: open; no grammar expansion.**

### CS math calls and numerical helper: 2026-09-13

This derived-proof increment follows `2051db5`. Five owning core/C/FMI/compiler
modules integrate finite floor, ordinary math-library call contracts, actual
`model_advance` execution and Solve duration/reported-time consequences.
The 27 new audit roots passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-prerequisites-package-gate-v1.log`, with all 845 inputs
unchanged. Earlier semantic definitions, emitters, mandatory
artifact contracts and audit roots are unchanged. The preceding 840-input
full gate remains the evidence for those unchanged artifacts; it was not
rerun for these derived proofs. Only these three status documents changed
after package acceptance. No new test suite was added.

The existing C11 §§7.6.3.1/7.12.9.2 mapping now has a computed result for every
finite floor argument and complete ordinary-call behaviors for the authored
library bindings. `fegetround` observes a supplied int32 mode; the native
library, target-header macro and fenv correspondence are still external.
FMI 3.0.2 stepping still needs guarded call integration, every status/output
path and communication-clock refinement. The helper theorem supplies actual
execution and its state frame, without assuming successful execution. The
source error at reported time includes the clock mismatch explicitly.

No MLS 3.7/eFMI Beta 1 syntax, initialization, lowering, solver policy or
generated member changes. No MISRA or other standards finding is closed.
**Stage decision: open; no grammar expansion.**

### Exact integer and Float64 conversions: 2026-09-13

This C-semantic checkpoint follows `cb94270`. It replaces integer `0`/`1`
special cases with an exact binary64 encoder for magnitudes below `2^53`, and
adds finite Float64→unsigned-size conversion with truncation and range checks.
The 32 core/C roots connect encoding fields, mathematical values, mathlib
floor/ceiling, nonfinite rejection and actual cast-expression evaluation.
The core/C/FMI/eFMI/compiler audit passed in
`build/c-factory/c-integer-package-gate-v3.log` with all 840 inputs unchanged.
The renewed full artifact gate passed in `build/c-factory/c-integer-full-gate-v1.log`,
also with all 840 inputs unchanged. Both checked archives are retained under
`build/c-factory/c-integer-artifacts-v1/`, with archive/member hashes and exact
comparisons beside them. C/header/GALEC and FMI XML match the ME checkpoint;
only the three eFMI generation identities and dependent references/checksums
changed. Only these three status documents changed after the full gate. All earlier
mandatory contracts and audit roots are retained; emitted C and grammar
are unchanged. Complete CS step execution is still open.

| Applicable obligation | Correspondence and boundary |
| --- | --- |
| [C11 N1570 §6.3.1.4](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), integer/real conversion | Exact integer encodings preserve the mathematical value throughout the stated range. Floating-to-size conversion uses truncation toward zero and representability; it does not use integer modulo for floating inputs. Other integer magnitudes remain outside this exact-conversion fragment. |
| C11 §§7.6.3.1/7.12.9.2, rounding environment and floor | The clauses were rechecked. The bounded-floor proof constructs a representable mathematical result; actual `fegetround`/`floor` calls and native bindings still require their contracts. The current CS body computes a sum before its step-cap rejection, so accepted-case arithmetic alone cannot cover all outcomes. |
| FMI 3.0.2 ME/CS | No interface, capability, initialization or numerical-step policy changes. Every earlier public-call proposition must remain valid under the extended conversion semantics. Repeated CS calls still require a relation between reported binary64 time, cumulative solver duration and source observations. |
| MLS 3.7, eFMI Beta 1 and MISRA C:2025 | No source/GALEC case, IR lowering, solver choice or generated member changes. This does not close initialization, essential-type, variable floating-comparison, ABI or whole-product findings. Proving an individual numeric cast is not a MISRA compliance decision. |

Floating exception flags/traps and later native compilation retain their
existing explicit boundaries. **Stage decision: open; no grammar expansion.**

### Creation through ME release: 2026-09-13

This five-root derived-proof checkpoint follows `8dc9e46`. The actual public
factory now supplies the handle, source default, ownership and caller-buffer
premises for initialization, admitted ME controls, termination and release.
The final lease map equals the original owners, and the combined frame
preserves cells outside the selected instance, outputs and reservation flag.
The FMI/compiler audit passed in `build/c-factory/me-creation-package-gate-v1.log`
with all 838 inputs unchanged. Existing emitters, semantics, mandatory contracts
and prior audit roots are unchanged; the previous full gate remains the
actual-artifact evidence. This derived-proof package snapshot is recorded
separately; no full artifact gate was rerun or new test suite added.

The existing FMI initialization/event/lifetime clause mapping is unchanged.
Creation still requires valid supplied storage, accepted identity buffers,
an available slot and explicit foreign bindings. The derived serial history
does not cover concurrent callers, host state updates/queries, numerical
integration, interspersed failures, reset or use after release. No MLS 3.7 or
eFMI Beta 1 semantics, advertised capabilities or generated bytes change.
No cross-standard or MISRA finding is closed. **Stage decision: open.**

### Initialization, ME controls and release: 2026-09-13

This derived-proof checkpoint follows `d054449`. One actual adapter witness
connects initialization, finite ME control histories, termination and release.
Initialization supplies the control invariant; ordinary typed writes preserve
atomic reservations, so the original lease supplies the later release without
an extra surviving-ownership premise. Exact calls, outputs, source initialization
and the final frame are retained. The 19 roots are integrated into the owning
C, FMI and compiler packages. Their audit passed in
`build/c-factory/me-lifecycle-package-gate-v1.log` with all 835 inputs unchanged.
Earlier emitters, semantics, mandatory contracts and audit roots are unchanged;
the full artifact gate was not rerun for these derived proofs. Their package
snapshot is recorded separately from the preceding actual-artifact evidence.

The preceding FMI 3.0.2 clause mapping remains applicable. This strengthens
the composition of the already checked initialization, event-iteration and
lifetime behavior; it adds no advertised capability or source case. Initial
ownership, native atomic bindings and valid instance storage remain explicit.
Creation, state setters/queries, importer integration, interspersed errors and
concurrent histories remain open. Released handles gain no subsequent-call
validity. MLS 3.7 and eFMI Beta 1 semantics and emitted artifacts are unchanged;
no cross-standard or MISRA finding is closed. The preceding full gate supplies
the unchanged artifact evidence. **Stage decision: open.**

### Mandatory ME control histories: 2026-09-13

This checkpoint follows `afb93ac`. It retains all earlier mandatory contracts
and adds event/continuous entry, completed integrator steps and discrete-state
updates with exact signatures, independent tokenization and complete represented
success/null/rejection/logging cases. The compiler consequence ties the calls
and their finite control histories to the actual adapter's pool and definition
table. The 92 added roots passed the C/FMI/compiler package audit in
`build/c-factory/me-package-gate-v5.log`, with all 829 inputs unchanged. The
full required gate passed in `build/c-factory/me-full-gate-v1.log` for the
same unchanged snapshot. Both checked archives are retained under
`build/c-factory/me-artifacts-v1/`, with exact member comparisons beside them.
C/header/GALEC and FMI XML match the time checkpoint; the three eFMI manifests
change only generation identities and their dependent references/checksums.
Only these three status documents changed after the full gate.

| Applicable obligation | Proof and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §2.3.5](https://fmi-standard.org/docs/3.0.2/), discrete iteration | The unit profile's discrete update returns all five Boolean flags false and writes positive binary64 zero to the next-time buffer. That numeric value is not a scheduled event when its defined flag is false. `MEHistory` requires a completed iteration before continuous entry and retains the actual returned values at each call. State setters, clocks and general event equations are not added. |
| FMI §§2.2.1/2.2.4, arguments and errors | All six output pointers are required; an undefined next-time result does not make its pointer optional. Complete null/lifecycle/missing-output cases follow the existing guards. Suppressed logging covers absent loggers; supplied logging retains every modeled returning effect and immutable diagnostics. Callback reentry/divergence and native private-memory frames remain open. |
| FMI §3.2.1, continuous mode and completion | Both completion flag inputs and the two false outputs are covered. Time/history updates retain positional completions and the last event, without an added monotonic-completion premise. Importer acceptance of state/input values and numerical integration must still be composed with this control-history result. |
| Memory and actual C | Reusable backend-c assignment/guard lemmas permit uninitialized output storage and compatible aliases. The trace derives writable storage after each call from one initial buffer bank outside the instance block. Public bytes, definitions and literal storage share the actual certificate. Native object layout, whole translation-unit correspondence and transitive no-heap/MISRA policy remain open. |
| MLS 3.7 and eFMI Beta 1 | Source equations, default initialization, DAE→GALEC→Solve and DAE→Solve ownership remain unchanged. No grammar, emitted C/GALEC/XML or numerical solver changes; no MLS/eFMI finding is closed by these proofs. |

The official FMI clauses were rechecked. The earlier draft's time/mode-only
projection was replaced before publication by the composed control history;
it is not evidence for all legal FMI host sequences. The source consequence
preserves initialization, not a claim that a time setter integrates the state.
No example-based proof substitute, new test suite or axiom-policy change was
introduced. K02–K05 and this spiral stage remain open; grammar expansion remains
blocked.

### Mandatory ME trial time: 2026-09-13

This checkpoint follows `c9cc627`. It adds the exact `fmi3SetTime` signature,
independent tokenization and complete represented call cases to the mandatory
actual-adapter contract. Every prior conjunct and audit root is retained.
The 25 new roots passed the FMI/compiler package gate in
`build/c-factory/time-package-gate-v1.log` with 815 unchanged inputs. The
strengthened actual-artifact contract then passed the full required gate in
`build/c-factory/time-full-gate-v1.log`, again with all 815 inputs unchanged.
Checked FMU/eFMU archives are retained in `build/c-factory/time-artifacts-v1/`.
Their C/header/GALEC and FMI XML bytes match the termination checkpoint; exact
eFMI manifest comparisons permit only fresh identities and dependent
references/checksums. The source reconciliation after this gate changes only
these three status documents. Grammar, emission, numerical semantics, audit
policy and native checks are unchanged.

| Applicable obligation | Added proof and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §3.2.1](https://fmi-standard.org/docs/3.0.2/), ME trial time | `TimeCalls.history_call` and `adapter_time_history` implement the independent history transition. Admission retains start time, second-last completion and last event entry as lower bounds. Retreating trial times remain allowed within that window; no monotonic-time premise is added. Prior history/storage and later event/completion composition remain explicit. |
| FMI §2.3.2, experiment stop | The optional stop remains inclusive. Finite out-of-window arguments take the actual error path. The authored finite-value/nonfinite-rejection policy is explicit; it is not presented as a new quotation from the standard. |
| FMI §§2.3.1/2.3.8, lifecycle and errors | Complete null, invalid-lifecycle, nonfinite and finite-window failures are proved. Suppressed logging includes a missing logger; supplied logging retains every modeled returning outcome and immutable diagnostic bytes. Callback reentry, divergence and private-storage frames remain open. |
| Actual C and source relation | `TimeCalls.FunctionContract` binds the public calls to the prepared pool/table; `adapter_time` locates the actual fragment. Updating time preserves the source initialization relation and model state. It does not prove that the unchanged state is the integrated solution at the new time. Native ABI and whole translation-unit correspondence remain open. |
| MLS 3.7 and eFMI Beta 1 | Source equations, initialization policy, DAE→GALEC→Solve and eFMI artifacts are unchanged. No new source case or MLS/eFMI finding is closed. |

The official FMI 3.0.2 clauses were rechecked for this checkpoint. The stage
remains open under K02–K05; neither the full artifact gate nor this standards review
authorize grammar expansion. No unit-test suite or axiom-policy change was
introduced.

### Mandatory termination and release: 2026-09-13

This increment follows `e0658fa`. It retains every previous adapter-contract
conjunct and requires the actual termination signature, printed tokenization
and complete represented call cases in the static object interface. No grammar,
emitter, numerical semantics, native check or axiom policy changes. The 15
new roots and strengthened artifact contract passed the full required gate in
`build/c-factory/termination-full-gate-v1.log`, with 809 unchanged inputs.
The actual archives are retained in `build/c-factory/termination-artifacts-v1/`.
C/header/GALEC and FMI XML bytes are unchanged; exact eFMI manifest comparisons
allow only fresh generation UUIDs/timestamps and their dependent references
and checksums. These generation differences do not indicate a new model or
production-code policy.

| Applicable obligation | Added proof and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §2.3.4](https://fmi-standard.org/docs/3.0.2/), termination from Initialized | `Termination.call_behaviors` uses the independent `Reference.Allowed` predicate: ME Event/Continuous or the admitted CS Step mode. `adapter_initialize_terminate` derives acceptance after initialization and retains exact heaps, model and clock. No source termination equations are admitted. |
| FMI §§2.2.4/2.3.8, error and final state | Null returns and invalid lifecycle calls are covered. Suppressed logging includes a missing logger; supplied logging retains every modeled returning outcome, trace, diagnostic bytes and the stuck case. Native callback behavior/private-storage frames and broader public histories remain open. |
| Actual C source and FMI signature | `AdapterContract` and its fixed Lean certificate generator now require `Termination.FunctionContract`; `adapter_termination` locates the exact fragment and obtains the same prepared pool/table. Header/layout/ABI and complete translation-unit correspondence remain open. |
| FMI §2.3.1, freeing a terminated instance; K02 ownership | `adapter_termination_release` obtains both public definitions from the same actual table. Termination preserves metadata and flags, then release discharges the original host lease. The combined frame excludes only the selected mode and atomic reservation flag. Native atomic-store refinement, host ownership and concurrent histories remain separate. |
| MLS 3.7 and eFMI Beta 1 | Source initialization policy and DAE→GALEC→Solve are retained. The new source theorem preserves the IVP selected by existing finite storage; it introduces no initialization/termination syntax. No MLS/eFMI open finding is closed. |

The four derived release roots passed the FMI/compiler package audit in
`build/c-factory/termination-release-package-gate-v1.log` with 811 unchanged
inputs. This follow-up retains every preceding emitter, mandatory contract and
audit root; its unchanged artifacts use the earlier 809-input full-gate evidence.
Released handles are not admitted for subsequent FMI operations. No new test
suite was introduced.

This increment does not close K02–K05 or authorize grammar growth. In
particular, successful termination's frame is not asserted for arbitrary
external logger effects, and its three-call composition is not a theorem
about arbitrary intervening simulation histories.

### Reset in the static runtime: 2026-09-13

On top of `5fc250c`, fifteen derived proof roots connect the actual adapter's
reset definition to the static object interface and then to both initialization
calls. The FMI/compiler package gate passed with 806 unchanged inputs in
`build/c-factory/static-reset-package-gate-v1.log`. The prior full artifact gate
supplies unchanged emitter/contract evidence; no grammar, emitted member,
mandatory contract or native check changes in this follow-up.

| Applicable obligation | Added evidence and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §2.3.1, reset](https://fmi-standard.org/docs/3.0.2/) | `adapter_static_reset_initialize` restores the Solve default, supplies writable initialization cells, and composes three complete calls through exact heaps to the source IVP. This covers model/lifecycle effects; equivalence of all host configuration to fresh instantiation, including logging policy, remains open. |
| FMI instance isolation and K02 ownership | `StaticReset.record_frame`, `restarted_other_instance` and `restarted_owners` preserve nested cells in other slots of the same array, metadata and reservation flags. Native layout, valid host ownership and concurrent execution remain separate. |
| MLS 3.7 §§4.9/8.6 | The stored finite default and unique completed real trajectory use the unchanged source/Solve initialization policy. No source equation is added; SR08 remains open. |
| eFMI Algorithm/Production Code | DAE→GALEC→Solve and its production/archive contracts are unchanged. No eFMI finding is closed by this FMI proof increment. |

All earlier audited roots remain required. Callback frames, other public calls,
complete host histories, whole-output provenance and MISRA/profile obligations
remain open, so grammar expansion remains blocked by the stage gate.

### MISRA C:2025 and static storage review

Reviewed 2026-09-13 against the user-supplied **MISRA C:2025, March 2025** PDF,
SHA-256
`42d1f700d83506566964131c6b618f4eba14782ea8fa7b7355924bb7c4b882aa`.
This is the primary MISRA baseline. The earlier supplied MISRA-C:2004 with
Technical Corrigendum 1 (July 2008 reprint), SHA-256
`f5325b58af9355bdab6a2c26495650715171bdcdb76b267d1255ff6c3f590fcd`,
is a historical reference. Neither PDF nor its extracted text is redistributed
or required by a repository build.

The 2025 Appendix A.1 inventory has **223 entries: 22 directives and 201 rules**.
There are 22 Mandatory, 154 Required, 46 Advisory and one Disapplied entry
(Rule 15.5). The IDs and categories were cross-checked against the main text.
Appendix A.2 separately records five withdrawn/renumbered rules. Inventory is
not enforcement: **MISRA compliance remains open and blocks the stage**.

Use the existing **C11** generation profile. Section 1.4 supports it, so the
2004-only C90 mismatch does not apply to this primary baseline. Rule 15.5 is
Disapplied in 2025; multiple returns need no deviation for that rule. Keep
proofs of every error/return path. The earlier floating equality concern
remains applicable under the 2025 essential-type Rule 10.1, with its stated
exceptions; it must not be carried forward under an obsolete rule number.

Section 1.5.2 requires MISRA Compliance:2020; §1.5.3 and Appendix E also apply
to code generators. Record implementation choices, essential-type strategy,
runtime failure handling and the user integration interface. Retain default
categories; no optional automatic-code recategorization or deviations have
been approved. Mandatory rules cannot be deviated (§3.4.1). The optional
[official recategorization plan](https://github.com/The-MISRA-Consortium/GRPs/)
is a separate reviewed decision. Deterministic compiler output and authored
adapter implementation must be scoped correctly; using a generator or having
Lean proofs alone does not establish qualification or an automatic exemption.

The compliance boundary includes generated C, adopted FMI/eFMI headers,
external interfaces and platform assumptions. Standard Library internals and
standard headers have the specific treatment in §1.5.4; FMI headers are not
C Standard Library headers. The project no-allocation requirement still needs
transitive library/callback evidence, even where MISRA does not require a
library's implementation to follow its coding rules.

| Finding | Guideline and observed evidence | Required disposition |
| --- | --- | --- |
| MC01 — C11/profile evidence | Required Rule 1.1 permits the chosen C11 edition. Current [build options](../packages/backend-fmi3/RumocaFMI3/BuildDescription.lean), [FMI types](../packages/backend-fmi3/vendor/fmi3/fmi3PlatformTypes.h) and shared C rely on binary64, integer widths and floating environment features. | Pin actual syntax, constraints, translation limits, types/ABI and compiler options; document implementation choices under Dir 1.1. C11 itself is no longer a mismatch. Compiler acceptance alone does not establish all these obligations. |
| MC02 — allocation | Required Dir 4.12 covers all dynamic allocation packages. Required Rule 21.3 specifically excludes allocator identifiers/macros. [Runtime.makeInstance/body](../packages/backend-fmi3/RumocaFMI3/Runtime.lean) emit `calloc`/`free`. | Remove them; no allocation waiver is proposed. Use a fixed array of fully typed, permanently existing instance objects, with bounded activation/deactivation and explicit field initialization. Prove ownership, exhaustion, isolation and reuse; review Dir 4.12 for the actual implementation. A custom allocator over a static byte arena is not an acceptable workaround. |
| MC03 — return structure, disposition | Rule 15.5 is Disapplied; the runtime uses early guard returns. | No single-exit rewrite or deviation is required by the 2025 baseline. Preserve all-path semantic proofs. Any older eFMI-referenced guideline has a separate disposition under MC08. |
| MC04 — essential types and floating comparison | Required Rule 10.1's operator table restricts floating `==`/`!=`, with exceptions for zero and positive/negative infinity. `Runtime.doStep` compares two variable floating values for the exact communication point and integer time grid. Integer literals are also used in some Boolean and floating expressions. | Review actual expression types under Rules 10.1–10.8. Preserve exact FMI time and solver behavior; an epsilon comparison is not an equivalent repair. Use typed emission for routine fixes and prepare an explicit numerical/deviation argument for any necessary remaining comparison. The exceptions do not cover arbitrary variable-to-variable comparisons. |
| MC05 — initialization and lifetime proof gap | Mandatory Rule 9.1 concerns automatic objects before reads; Rule 9.7 separately concerns atomics. Required Rule 18.6 and Dir 4.1 address escaped automatic storage and runtime failures. Existing typed loads/stores and frames do not yet establish complete creation/lifetime and native layout correspondence. | Bind actual storage declarations and initialization to complete calls. Initialize all reused fields and any synchronization objects correctly, including Rule 22.14 where applicable. Record RTOS startup guarantees. No Mandatory-rule deviation is possible. |
| MC06 — effects, recursion and concurrency | Required Rules 13.2/13.5 concern evaluation order and conditional effects; 17.2 excludes recursive call chains. Required Dir 5.1–5.3 address races, deadlocks and dynamic thread creation; 21.25 requires sequentially consistent synchronization. | Prove order independence where C leaves order open, effect constraints and an acyclic generated call graph. Prove safe shared activation/release, including the chosen atomic semantics and implementation. Keep synchronization outside numerical stepping and avoid hidden library locks. No generated threads are planned; host callbacks/reentry and native RTOS primitives need explicit boundaries. |
| MC07 — identifiers, pointers and provenance | Rules 5.1–5.10, 11.1–11.6/11.8–11.11 and 18.1–18.10 require profile-specific namespace/type/pointer evidence. Required Dir 3.1 also requires documented requirement traceability. Source spans alone do not identify every generated policy requirement. | Connect existing name, conversion, bounds and origin proofs to the exact rules and actual preprocessed interfaces. Preserve generated-rule ancestry. Symbolic pointer cells and a 63-character name check alone cannot close the whole-product obligations. |
| MC09 — implicit pointer guards | Required Rule 11.11 prohibits implicit comparison of pointers with null. The shared `instancePrefix` now emits `m == ((void *)0)` with null-value, printer and branch-preservation proofs. Other instance/name/callback pointer guards remain implicit. | Partial progress only. Complete the remaining explicit comparisons and essential-type review. Preserve short-circuiting, logger behavior and all existing function contracts; a textual replacement without semantic preservation is insufficient. |
| MC08 — eFMI references and generator process | eFMI 1.0.0 Beta 1 §5.2 references MISRA AC AGC for generated code; its GALEC rules also name MISRA C:2012. MISRA C:2025 §1.5.2 and Appendix E impose additional compliance/generator documentation. | Map the separate normative references and review their applicable text. The 2025 book does not silently replace eFMI's references or close SR07. Complete the generator and product compliance documentation and independent review. |
| MC10 — nested aggregate address scope | The former `CMemory.Address` flattened indices across member selection. It now records the containing element's offset at each selection and starts the selected member's local offset at zero. Ten new roots, all affected packages and the required main artifact gate pass. | The modeled address correction is complete; both checked archives retain identical C/header/GALEC bytes. Keep bounds, valid native objects, leaf types and layout separate. Arbitrary-depth descendant and store-frame proofs establish structural isolation for the planned static array; they do not implement its native storage or concurrency. |

The initial enforcement plan is below. Each group must become a separate entry
for every applicable directive/rule before claiming compliance, with its
category, language applicability, analysis scope, independent predicate,
evidence, actual-file coverage, reviewer and any approved deviation. **All
groups retain open work; Rule 15.5's Disapplied disposition is explicit.**
“Formal” describes the intended evidence, not an existing MISRA theorem.

| Guideline inventory | Planned enforcement and boundary |
| --- | --- |
| Dir 1.1–1.2 | Implementation choices and language-extension documentation. |
| Dir 2.1 | Actual build diagnostics and pinned toolchain/options. |
| Dir 3.1 | Source and generated-policy requirement traceability through actual outputs. |
| Dir 4.1–4.15 | Runtime-failure argument, external inputs, library calls, coding policy and whole-call-graph no-allocation evidence. |
| Dir 5.1–5.3 | Race/deadlock freedom and no dynamic thread creation; host integration assumptions. |
| Rule 1.1, 1.3–1.5 | C11 syntax, constraints, behavior and permitted feature profile. |
| Rule 2.1–2.8 | Reachability, statement purpose and unused declarations. |
| Rule 3.1–3.2 | Actual-source comment/line-splicing policy. |
| Rule 4.1–4.2 | Proved literal escapes and preprocessor-sensitive source checks. |
| Rule 5.1–5.10 | Namespace, scope, significance, uniqueness and reserved-name checks. |
| Rule 6.1–6.3 | Bit-field type, width and union restrictions. |
| Rule 7.1–7.6 | Literal spelling, integer suffixes and string literal treatment. |
| Rule 8.1–8.19 | Declarations, prototypes, linkage, qualification, atomic/alignment usage and header evidence. |
| Rule 9.1–9.7 | Definite initialization, initializer shape and atomic initialization. |
| Rule 10.1–10.8 | Independent essential-type/operator/conversion model and emitter preservation. |
| Rule 11.1–11.6, 11.8–11.11 | Pointer/cast permissions and actual typedef/layout correspondence. |
| Rule 12.1–12.6 | Operator grouping, shifts, unsigned arithmetic and permitted object access. |
| Rule 13.1–13.6 | Expression effects, evaluation order and discarded computations. |
| Rule 14.1–14.4 | Loop and Boolean controlling-expression policy. |
| Rule 15.1–15.7 | Branch/jump/block structure; 15.5 is Disapplied. |
| Rule 16.1–16.7 | Switch grammar, labels, termination and discriminant constraints. |
| Rule 17.1–17.5, 17.7–17.13 | Call graph, prototypes, arguments, results and restricted function features. |
| Rule 18.1–18.10 | Pointer/array operations, nesting and object lifetime. |
| Rule 19.1–19.3 | Aggregate assignment overlap and union representation/initialization. |
| Rule 20.1–20.15 | Actual preprocessing, macros, conditional definitions and reserved library names. |
| Rule 21.3–21.26 | Library facilities/arguments, allocation prohibition and synchronization semantics. |
| Rule 22.1–22.20 | Resource lifecycle, error indicators and thread/synchronization objects. |
| Rule 23.1–23.8 | Generic selection/type-generic macro policy. |

Appendix A.2's withdrawn IDs are tracked rather than assigned invented current
requirements: Rule 1.2 → Dir 1.2; 11.7 → 11.4; 17.6 → 17.5;
21.1 → 20.15; 21.2 → 5.10. The grouped inventory covers each of the 223 current
IDs exactly once; this is bookkeeping evidence, not a compliance percentage.

Prefer independent Lean predicates with sound checkers and universal emitter
preservation proofs, made mandatory in the actual-artifact contract. Existing
parser/printer and execution proofs may supply premises after exact mapping.
Analyzer/manual/platform evidence fills boundaries not yet formalized. The
RTOS numerical kernel must use supplied storage, have explicit operation and
storage bounds, and avoid OS services, heap calls, hidden locks and incidental
I/O. Bounded object activation/release and its concurrency proof remain K02 in
[the roadmap](roadmap.md#k02--replace-heap-allocation-with-proved-static-instance-storage).

### Explicit null comparison and storage prerequisites

This increment follows `784f45b`. It changes only the shared FMI instance guard
from `!m` to `m == ((void *)0)`. Rule 11.9 permits the explicitly cast zero
constant; a `NULL` macro is not required for this spelling. The independent
C expression grammar and null-value proof bind the printed expression to the
authored C semantics. The shared branch theorem preserves execution for every
represented pointer value; the existing complete-call contracts remain required
for the changed actual adapter. Literal pooling and interface extension preserve
the syntactic constant distinction: a variable containing integer zero is not
accepted as a null pointer constant. C11 6.3.2.3p3–4 and 6.5.9p6 supply the
reviewed null-pointer meaning. Equality between two non-null symbolic pointers
and broader integer constant expressions remain outside this expression slice.

`CStorage` proves that internal modeled execution preserves the supplied cell
domain, types and permissions. This does not prove termination of unsupported
allocation calls or constrain foreign effects; it is not a no-heap certificate.
`StaticSlots` proves bounded serial search, exclusion and release/reuse of fixed
slots. C atomics, concurrent scan behavior, caller ownership and actual instance
storage still need refinement proofs. In particular, serial exhaustion cannot
be inferred from a scan interleaved with other callers releasing slots.

The current address representation's nested-index collision has a universal
Lean review witness in `build/c-static-storage/AddressScope.lean`; this records
MC10 without introducing a new admitted source case. The shared C, FMI and
compiler package checks pass in `build/c-static-storage/package-v3.log`, with
44 added audit roots and all earlier roots and the axiom policy retained.
The required actual-artifact gate passed in
`build/c-static-storage/full-gate.log`, including all 13 existing native FMI
groups and the eFMU checks. All 710 source inputs and the file set remained
unchanged throughout the gate. Both archives are retained under
`build/c-static-storage/artifacts/`. Compared with `784f45b`, only the
70 shared instance guards in `sources/fmi3.c` changed; all other C, header
and GALEC bytes are identical (`build/c-static-storage/artifacts.log`).
No MISRA finding other than the named shared guard is
closed, no grammar is added, and no full compliance claim follows.

### Atomic reservation helper: standards impact

This increment follows `a1ceae5` and leaves source grammars, numerical IRs and
production emitters unchanged. C11 7.17.1p5, 7.17.7.1 and 7.17.7.3 supply the
selected non-explicit store/exchange value and ordering contracts; 7.17.3p6/p12
specify their SC ordering and preceding modification. Static atomic Boolean
initialization and the always-lock-free macro value are reviewed against
7.17.2.1p2 and 7.17.5p1. Native declarations and bindings are still required.
See the [WG14 C11 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).

MISRA C:2025 Rule 21.25 requires the selected sequentially consistent order.
The new helper uses two declared unsigned operands for counter addition
(10.4), representable integer constants for size initializers (10.3), and
explicit Boolean casts of zero/one under 10.5's exception. It performs at most
one exchange per slot and contains no recursive C call. This is a scoped
review, not a whole-product essential-type or MISRA compliance certificate.

The helper's actual CTree executes through the shared typed call scheduler,
including fresh parameter binding, local initialization, the bounded loop and
an arbitrary caller continuation. Admitted flag cells yield termination and
an exact sequential trace/result, with frame and storage-preservation proofs.
The shared printer binds the actual function text to its independent token
grammar. The new `_Bool` and `volatile` productions retain all prior cases.
The independent FMI slot reference is refined by the atomic operations and
the complete sequential scan. All C/FMI/eFMI/compiler package checks pass in
`build/c-atomics/package-check.log`; 38 roots are added and none removed.
The required main artifact gate passed in `build/c-atomics/full-gate.log`,
including the existing native FMI and eFMU checks. All 720 source inputs
and the complete file set remained unchanged throughout the run. Both
archives are retained in `build/c-atomics/artifacts/`; every C/header/GALEC
member is byte-identical to `a1ceae5` (`build/c-atomics/artifacts.log`).

MC05/MC06 and K02 remain open: production uses `calloc`/`free`, and this helper
is not yet emitted by its factory. Complete native object declarations,
stdatomic macro/header binding, concurrent ownership, full initialization on
reuse and creation/release must be composed with actual artifacts. A failed
concurrent scan need not observe one globally full snapshot. Requiring
`ATOMIC_BOOL_LOCK_FREE == 2` in the eventual native profile will not by itself
prove operation latency, implementation correctness or whole-program no-heap
behavior. The modeled `size_t` remains 64-bit; native width/ABI interpretation
requires its existing K04 evidence. No MLS/FMI/eFMI expansion is authorized.

### Identity validator and storage foundations: standards impact

This increment follows `00de05b`. It retains the existing name/token acceptance
condition and moves its string calls into an explicitly sequenced private
helper. C11 7.24.6.3 specifies length before the terminating null character;
7.24.5.6 specifies the maximal accepted prefix; 7.24.4 and 7.24.4.2 specify
unsigned-character ordering and the sign of a comparison result. The modeled
`strcmp` permits every representable result with that sign, not only -1/0/1.
The selected target remains eight-bit characters, 32-bit `int` and 64-bit
`size_t`; native-library/header correspondence is an explicit boundary.
See the [WG14 C11 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).

The complete helper proof covers parameter/local initialization, explicit
null rejection, all three library calls, unchanged memory and arbitrary caller
observations. The independently defined acceptance predicate requires a byte
outside the supplied whitespace set and equality to the supplied expected
token. The actual factory supplies its prepared token and existing six-byte
whitespace literal. The mandatory adapter certificate binds the helper's
printed fragment, definition table and complete execution contract. Its
library-name check and environment-construction theorem rule out a vacuous
linkage premise. Native buffer validity and the enclosing factory still need
their separate contracts. The helper's explicit null comparisons advance MC09;
remaining logger/instance pointer guards and whole-product essential types are
open. No no-heap guarantee follows from modeled library purity.

The accompanying shared-memory/interleaving proofs preserve private atomic
flags through ordinary C steps and relate an explicit slot-ownership protocol
to those steps. They do not prove that all production histories satisfy that
protocol, or that native C11/RTOS execution refines this scheduler. MC02,
MC05/MC06 and K02 remain open, including actual `calloc`/`free` removal.
All affected package checks pass in `build/c-factory/identity-packages-v1.log`,
with 60 added roots, no removed roots and unchanged axiom auditing. The required
full artifact gate passed in `build/c-factory/identity-full-gate.log`, including
both actual archives, with all 743 source inputs unchanged. The retained
code-member comparison under `build/c-factory/identity-artifacts/` shows only
the identity helper and its two factory call sites changed in FMI C; numerical
C and eFMI C/GALEC are unchanged from `00de05b`. No source grammar, numerical behavior or
FMI/eFMI capability is expanded; the recurring standards gate remains closed.

### Public factory admission: standards impact

This increment follows `13fb2a6` and changes proofs/certification without changing
the emitter. ME and CS retain the pinned header signatures. The shared typed-call
semantics performs fresh parameter binding; CS's unsupported-capability guard
precedes identity validation. The name/token predicate, diagnostics and public
capabilities are unchanged. C11 parameter adjustment/conversion, null-pointer,
string-library and readonly-object assumptions remain as previously recorded.

The mandatory actual-adapter contract now binds both public function fragments
to their execution table and installed literal pool. All null/nonnull identity
decisions and the rejected CS capability path have complete logging/silent
proofs. Represented callback memory effects and missing outcomes are retained.
Prepared diagnostic bytes are protected by readonly storage; this does not
establish a frame for private writable instance fields. Native callback
reentrancy/divergence and header/ABI correspondence remain explicit boundaries.

C/FMI/eFMI/compiler package checks pass in
`build/c-factory/factory-contract-packages-v1.log`, with 50 added roots, none
removed and unchanged axiom auditing. The required full artifact gate passed
in `build/c-factory/factory-full-gate-v2.log`, with all 760 inputs unchanged.
The retained FMU and eFMU under `build/c-factory/factory-artifacts/` have identical
C/header/GALEC members to `13fb2a6`. An earlier generated membership-proof error
was rejected by the audit and corrected before this successful gate.

FMI 3.0.2 [§2.3.1](https://fmi-standard.org/docs/3.0.2/#fmi3InstantiateModelExchange)
requires diagnostics on failed instantiation subject to the explicit prohibition
on callbacks when logging is disabled. Null callbacks denote missing support.
The [§2.2.1](https://fmi-standard.org/docs/3.0.2/#requirements-for-implementations-of-the-c-api)
restriction on log-callback reentry is a host obligation. These clauses were
rechecked for the admission contract; native callback correspondence remains
open. The six-byte whitespace predicate is proved as the emitted policy;
its correspondence to the prose name requirement remains part of K05 review.
K02, MC02 and the whole-product MISRA/FMI/eFMI findings remain open: successful
creation/release, typed static storage and `calloc`/`free` removal are unfinished.
There is no MLS grammar, numerical or capability expansion; the recurring
standards gate remains closed.

### Hierarchical subobject correction: standards impact

This increment follows `b478606`. Each `Address.member` preserves its containing
element's index in the member path. The next array offset is local to that
member, so it cannot be confused with an outer instance index.
`member_index_eq_iff` recovers both indices and the member name; `InRecord`
supports arbitrary member depth and local array offsets. `store_other_record`
uses the actual typed store and proves preservation of another enclosing
record's descendants, including nested model fields and tensor cells.
Tensor-region preparation and view separation use the same representation.

The reviewed C rules are array selection (C11 6.5.2.1p2), member selection
(6.5.2.3p3–4), and bounded pointer displacement (6.5.6p8).
See the [WG14 C11 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
The authored model still requires valid objects, bounds, leaf types and
lifetimes from a separate layout interpretation. It does not infer unequal
native pointer values from every pair of distinct symbolic paths: aggregate
and initial-member pointers, non-null pointer comparisons and general nested
C array decay have separate obligations. This change addresses array indices
across named member selection, without adding a new source grammar case.

All ten added roots and existing C/FMI/eFMI/compiler checks pass in
`build/c-static-storage/address-package-v3.log`. The exact five changed
implementation/audit files are recorded in `address-promote.json` in the same
directory. The required main artifact gate passed in
`build/c-subobjects/full-gate.log`, including the existing native FMI and
eFMU checks. All 711 source inputs and the complete file set remained
unchanged throughout the gate. Exact archives are retained in
`build/c-subobjects/artifacts/`; all C/header/GALEC members are byte-identical
to `b478606` (`build/c-subobjects/artifacts.log`). Numerical operations,
IR lowering, emitters and metadata are unchanged. Actual static declarations,
creation/release, concurrency, native layout and whole-stage compliance remain
open; no dynamic-allocation removal is claimed.

### Complete initialization calls: standards impact

This correction follows `d519438`. Source/GALEC grammars, indexed IRs, numerical
Solve programs and eFMI emitters are unchanged. The FMI unit adapter now admits
equal start/stop and ignores unused tolerance. Its full-call and source
contracts become mandatory in the actual-file certificate; this is not a
grammar expansion or a whole-stage conformance claim.

| Obligation | Coverage and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §2.3.2](https://fmi-standard.org/docs/3.0.2/#fmi3EnterInitializationMode), arguments | Finite start, optional finite inclusive stop, and exact raw-bit admission/rejection are proved. CS may ignore tolerance; the ME rationale is the absence of an internal tolerance-controlled algorithm in this unit model. This does not assert universal permission for other solvers or a requirement to accept arbitrary inputs. |
| FMI §§2.3.2–2.3.3, initialization | Complete typed entry/exit establish clock/history and the reference ME/CS mode while preserving the actual model state. Old clock payloads may be uninitialized. Allocation must still establish storage and the default state. |
| [FMI §§2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions) and [2.3.1](https://fmi-standard.org/docs/3.0.2/#FMUStateSettable), failures | Illegal arguments/lifecycle calls reach Error and the Terminated write. Disabled logging and all represented returning logger outcomes are characterized. Null handles return Error defensively. Callback ownership/reentry and native ABI remain outside this call model. |
| FMI §3.2.1, time | The initialized heap discharges the existing SetTime guard's reference window, including its inclusive stop. Complete subsequent public-call histories remain separate. |
| MLS 3.7 §§4.4.2.1 and 8.6 | The unmodified declaration leaves its initial state free. The compiler default is zero; a finite host override is preserved. The source contract ties the stored value to its unique Real trajectory at the supplied time origin. No binding/modifier syntax is added; S01/SR08 are not closed. |
| eFMI 1.0.0 Beta 1 | Algorithm/Production Code, initialization program, manifests and archive layout do not change. Their prior actual-artifact contracts remain required by the full gate. |

Architecture was checked against Rust Rumoca `bc71577f`, including
`crates/rumoca-ir-solve/src/model.rs`: the executable model and initialization
plan remain Solve responsibilities. These calls own FMI time/lifecycle state
and do no source resolution, shape inference, scalarization, DAE lowering or
solver selection. The reusable LALR parser remains unchanged.

Composition builds in `build/c-initialization/composition-v2.log`. All 51 added
roots and affected package checks pass in `build/c-initialization/package-v1.log`.
The required full artifact gate passed in `build/c-initialization/full-gate.log`
with all 706 inputs and the complete file set unchanged. Both archives are
retained in `build/c-initialization/artifacts/`; their hashes are recorded in
[the FMI contracts](fmi3/contracts.md#complete-initialization-calls). Compared
with `d519438`, only the FMI initialization-entry body changed; every other
C/header/GALEC member is identical. All 13 native FMI groups pass, including
the extended argument/atomicity group, with no new suite.
The strict `above_iff` policy root is replaced by the inclusive proof; all other
earlier roots and the axiom whitelist are retained. **Stage decision: open;
grammar growth remains blocked.**

### FMI parameter types and typed call entry: standards impact

This increment follows `fe4ebef`. Both EBNFs, LALR admission, IR lowering,
initialization and emitted C/GALEC/XML remain unchanged. The reusable mechanisms
are width-parametric unsigned conversion and parameter-list-parametric typed
call entry. The FMI dictionary adds the missing adjusted pointer spellings and
unsigned 32-bit value references; it does not add general source integer syntax.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| C11 [N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §6.3.1.3p1–2 | `CUnsigned.Converts` specifies the in-range integer congruent modulo one more than the maximum value. Uniqueness, identity for in-range values, BitVec correspondence and target conversion/store/load proofs cover arbitrary widths and integer inputs. Actual C widths and typedef meanings remain adapter assumptions. Signed overflow, floating-to-integer and pointer-to-integer conversions are outside this increment. |
| N1570 §§6.7.6.3p7 and 6.9.1p10 | The call theorem uses the existing array-parameter adjustment, derives fresh named value/type environments and preserves the caller's heap/continuation at entry. It quantifies over convertible arguments and proves those lists exist. Whole body behavior, pointee types/layouts and external declarations remain separate. |
| FMI 3.0.2 ME/CS, [§§2.2.1–2.2.3](https://fmi-standard.org/docs/3.0.2/#platform-dependent-definitions) | The pinned header specifies `fmi3ValueReference` as `uint32_t`; pointer aliases and callback parameters are opaque symbolic addresses in the authored machine. The actual-file checker now kernel-checks readiness of every collected signature; the contract includes every helper too. It retains all previous grammar/reset fields. Header interpretation, callback execution, allocation, remaining public-call behavior and SR04/SR05/SR07 stay open. |
| MLS 3.7 | No admission, source equations, initialization selection, Real refinement or provenance changes. The existing unit clause map and S01/SR08 findings carry forward. |
| eFMI 1.0.0 Beta 1 | The shared target adds an unsigned conversion constructor; eFMI selects its existing dictionary. No Production/Algorithm Code member, manifest, lowering or archive contract changes. Existing coding-guideline and SR07/SR08 findings carry forward; downstream proofs and artifact checks must pass. |

All 26 new roots and affected packages pass
`build/fmi-types/package-audit-v2.log`. The signature review now reports zero
missing parameter types among the 75 APIs. The strengthened actual-file checker
passes in `build/fmi-types/actual-fmi.log`. The required full gate passed in
`build/fmi-types/full-gate.log`, with all 629 inventoried inputs unchanged and
both actual archives checked. Exact archives and hashes are retained in
`build/fmi-types/artifacts/`; C and GALEC members match `fe4ebef`
(`code-member-comparison.log`). No new example-based suite is added. **Stage decision: open;
grammar growth remains blocked.**

### Float64 setter: standards impact

This increment follows `636264f` and changes proofs and mandatory actual-file
contracts. The source EBNFs, admitted unit profile, IRs, initialization policy,
C/GALEC/XML emitters and archive layout are unchanged. Pinned FMI 3.0.2 clauses
and its schema were reviewed for the state setter.

| Obligation | Coverage and remaining boundary |
| --- | --- |
| FMI §§2.2.7.1–2.2.7.2, type and serialization | Complete validation precedes all state writes. Accepted requests select only reference 1 and retain finite payload bits, including signed zeroes. Request buffers reuse the tensor-memory relation; nValues=nValueReferences remains specific to scalar variables. Repeated requests leave the final value. No duplicate-setting prohibition was found in this section; the separate prohibition for InitialUnknown entries does not apply to API buffers. |
| FMI §§2.3.2–2.3.3, setting start values | XML identifies the selected variable as local, continuous and initial=exact. Instantiated/Initialization writes implement the semantic state update and preserve every other cell. Allocation and the complete initialization history still require composition; this does not close S01/SR08. |
| FMI §§2.3.5 and 3.2.1, ME state writes | Event Mode permits continuous states with reinit=false; Continuous-Time Mode permits setting continuous states. The XML judgment follows ModelStructure to the same declaration selected by numeric reference, without assuming unique names. It checks the exact/local attributes and interprets omitted reinit as false under the pinned [FMI 3.0.2 schema](https://raw.githubusercontent.com/modelica/fmi-standard/v3.0.2/schema/fmi3AttributeGroups.xsd). |
| FMI §§2.2.4 and 2.3.1, errors and logging | Null instances return Error defensively; empty requests permit null arrays. Lifecycle/array/first-entry failures reach the actual helper before state writes. Unknown references do not require a value load. All represented returning logger outcomes/absence and disabled logging are covered. Actual host storage, callback effects/reentry, ownership and native ABI remain explicit boundaries. |
| MLS 3.7 | No source grammar or initialization syntax is added. The setter supplies a finite state to the existing mathematical Real equation; the same Flat/DAE/Solve numerical consequence is retained. Complete source/initialization histories remain open. |
| eFMI 1.0.0 Beta 1 | The reusable memory overwrite lemma and FMI adapter proofs add no eFMI behavior. Prior GALEC/Production C/XML/archive contracts remain required. The full gate passes and actual C/header/GALEC members match `636264f`. |

The setter uses the state-specific permissions despite the broader
local-variable restriction in §2.4.7.1. This cross-clause interpretation remains
part of the prose review; Lean proves the authored contract.

Enabled logging requires a represented callable logger. FMI §2.3.1 permits
null callback pointers for unsupported functionality and leaves use of that
functionality undefined. This contract covers enabled logging with the supplied
callback and disabled logging with either pointer value; it does not claim a
logging guarantee for an enabled but missing callback.

Architecture was checked again against Rust Rumoca `bc71577f`, particularly
`crates/rumoca-ir-solve/src/model.rs`: Solve owns derivative programs,
initialization programs and layouts. The setter consumes prepared state
storage and performs no resolution, shape inference, solver selection or
per-element IR lowering. All 51 new roots and affected packages pass in
`build/c-float64-set/package-v1.log`. The required full artifact gate passed in
`build/c-float64-set/full-gate.log`, with all 694 source inputs unchanged and
both actual archives checked. Retained artifacts are in its `artifacts/`
directory; all C/header/GALEC members match `636264f`.
No new test suite is added.
**Stage decision: open; grammar growth remains blocked.**

### Float64 getter: standards impact

This integration follows `8346cad`. The source EBNFs, admitted unit profile,
IRs, initialization policy, C/GALEC/XML emitters and archive layout are unchanged.
The pinned FMI 3.0.2 text was reviewed for the applicable getter obligations.

| Obligation | Coverage and remaining boundary |
| --- | --- |
| FMI §§2.2.7.1–2.2.7.2, retrieval and serialization | The complete public call validates all numeric references before writing concatenated results in request order, preserving duplicates. All three declared variables are scalar; only for this profile does nValues equal nValueReferences. Reusing the tensor-memory buffer judgment does not license tensor-variable serialization. |
| FMI §2.2.7.2, type and identity | Independent XML lookup resolves a unique continuous scalar Float64 declaration by decimal reference, and agrees with C selection of time/state/derivative. Names come from the prepared Solve model, including its time-name collision rule. The decimal judgment covers nonempty ASCII digits including leading zeroes; complete XSD lexical/schema conformance remains separate. |
| FMI §§2.3.2–2.3.3, start values and initialization | The getter returns represented time/state and evaluates the constant RHS. This does not prove those stored values satisfy the lifecycle's start/current-value invariants. Allocation, host setters and complete initialization composition remain open; the getter proof does not close S01/SR08. |
| FMI §§2.2.4 and 2.3.1, errors and logging | Empty arrays may be null. Invalid length/pointer and first invalid reference reach the real failure helper before any output write. All represented enabled logger outcomes/absence and disabled logging are characterized. Actual caller storage, callable bindings, native effects/reentry and ownership remain explicit boundaries. |
| MLS 3.7 | The source remains one Real state with unit derivative. The same Flat/DAE/Solve chain supplies the derivative's exact Real meaning. No declaration, initialization syntax or mathematical/IEEE domain expansion occurs. |
| eFMI 1.0.0 Beta 1 | Generic event-loop composition adds no emitter behavior. Existing GALEC, Production C, manifest and actual archive contracts remain required. The downstream full gate passed; every C/H/ALG member matches the prior checkpoint. This does not close the remaining prose-standard obligations. |

Architecture review against local Rust Rumoca `bc71577f`: `SolveProblem` owns
continuous derivative and initialization programs together with their layouts.
This Lean increment consumes prepared Solve and reuses generic C loops and
tensor-memory frames; it performs no source resolution, shape inference,
per-element IR lowering or solver selection. All 58 added roots and affected
packages pass in `build/c-float64-get/package-v2.log`. The required full gate
passed in `build/c-float64-get/full-gate.log`, with all 686 inputs unchanged.
Both actual archives are retained in its `artifacts/` directory, and all
C/H/ALG members match `8346cad`. No new test suite is added. **Stage decision: open;
grammar growth remains blocked.**

### Continuous-state derivative query: standards impact

This proof integration follows `035ad1d`. The EBNFs, production admission,
IRs, initialization, emitters and archive layout are unchanged. Pinned FMI 3.0.2
§§3.2.1 and 2.4.7 were reviewed directly for the getter and derivative order.

| Obligation | Coverage and remaining boundary |
| --- | --- |
| FMI §3.2.1, first-order derivative query | The actual public call follows `model_rhs` into the verified numerical C statements and writes the prepared Solve derivative. The output frame is explicit; no solver/time update occurs. The admitted constant RHS is provably finite, so this slice has no numerical-failure case. The bracketed Discard advice is not claimed as a generalized failure policy. |
| FMI §2.4.7, ModelStructure order | Independent XML lookup resolves ordered ContinuousStateDerivative entries through unique derivative/state declarations. The derivative list's state projection agrees with the state-access order. Array serialization is outside this scalar judgment. |
| FMI lifecycle, §§2.2.4 and 2.3.1 | The independent ME relation governs legal modes; wrong kinds/modes, wrong counts and null buffers reach the actual Error/log helper. Null handles are covered defensively. Enabled callback execution requires callable binding; disabled execution permits a null logger. Native effects, reentry and ownership remain boundaries. |
| MLS 3.7 | Existing Flat/DAE/Solve theorems relate the exposed derivative's Real value exactly to the source equation. No grammar, Real-domain or initialization change; S01/SR08 remain open. |
| eFMI 1.0.0 Beta 1 | The shared C increment only lifts existing numerical statement executions into the event scheduler. GALEC, Production Code, manifest and archive contracts remain required. Their downstream gate and byte comparison remain separate evidence. |
| Actual artifact and header boundary | Both actual adapter fragments, numerical C contract, XML order and eventful literal preservation are mandatory for the same Solve/table/pool. The fixed checker proves membership and numerical-name freshness for its quoted candidates; this does not verify header parsing, typedef/layout or ABI correspondence. |

Architecture review against Rust Rumoca `bc71577f`: `SolveProblem` owns the
continuous derivative program and initialization data. The Lean backend still
consumes prepared Solve; it adds no DAE resolution, source lookup, shape inference
or per-element lowering. Generic C scheduler and public-call prefix proofs are
reused. All 41 additional roots and affected packages pass in
`build/c-derivatives/package-v1.log`; the required full artifact gate passed in
`build/c-derivatives/full-gate.log`, with all 675 inventoried inputs unchanged.
Both actual archives are retained in `build/c-derivatives/artifacts/`; their C,
header and GALEC members match `035ad1d` (`artifacts.log`).
No new test suite is added. **Stage decision: open; grammar growth remains blocked.**

### Continuous-state access: standards impact

This proof increment follows `ca178d0`. Production grammar, source semantics,
IR lowering, C/GALEC emitters, metadata and archive layout are unchanged.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| [MLS 3.7 §4.9.1](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html#real-type) | Stored Real values must be finite. The setter accepts every finite binary64 value, preserving signed zeros, and rejects non-finite encodings. Ideal continuous trajectories remain a separate reference; source initialization findings S01/SR08 remain open. |
| FMI 3.0.2 [§3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3SetContinuousStates) and §2.4.7 | State calls obey the independent ME lifecycle relation and the XML derivative/state reference order. Count/pointer and non-finite checks precede state writes. `StateMetadata` resolves that order uniquely for scalar continuous Float64 declarations; array serialization is excluded. |
| FMI §§2.2.4, 2.2.7.3 and 2.4.4 | Illegal calls use Error. Domain failures may use Error or Discard; the bracketed setter guidance recommends Discard for rejected values. Our reviewed policy is fail-stop Error for non-finite Modelica state values, not a claim that FMI mandates that choice. The helper changes mode and respects logging; it does not implement Discard. |
| Actual adapter boundary | Both printed function contracts, same-table literal preparation and all represented error callback outcomes become mandatory. Caller storage, finite internal state, atomic host effects, header meaning and native ABI remain explicit assumptions or open obligations. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code or artifact contract changes. Existing clause maps and SR07/SR08 findings carry forward, with the full downstream gate still required. |

Architecture review against `~/git/rumoca` at `bc71577f`: its SolveProblem owns
prepared continuous and initialization data, with no DAE evaluation in Solve
consumers. This increment keeps the Lean backend on prepared Solve and uses
shared public-call proofs; it introduces no solver selection, source resolution,
shape inference or per-element lowering in the backend.

All 39 additional roots and affected package checks pass in
`build/c-state-calls/package-v1.log`; the required full artifact gate passed
in `build/c-state-calls/full-gate.log`, with all 667 inventoried inputs unchanged.
Both actual archives are retained in `build/c-state-calls/artifacts/`; their C,
header and GALEC members match `ca178d0`. No new test suite is added. **Stage decision: open; grammar growth remains blocked.**

### Nominal queries: standards impact

This proof integration follows `54618eb`. Both EBNFs, LALR admission, source
and Solve semantics, initialization policy and emitted members are unchanged.
The generic C partial-body theorem and failure-statement contracts are reused
for public-call composition. The pinned FMI 3.0.2 clauses below were checked
directly against the published specification for this increment.

| Obligation | Coverage and boundary |
| --- | --- |
| FMI 3.0.2 [§2.3.3, nominal query](https://fmi-standard.org/docs/3.0.2/#fmi3GetNominalsOfContinuousStates) | Allowed ME calls return OK and store the positive decoded default 1. The independent lifecycle guard, exact count, null buffer, rejected modes and defensive null-instance cases have complete call proofs. Valid caller storage and declared instance fields remain premises. |
| FMI 3.0.2 [§3.2.1, continuous-state order](https://fmi-standard.org/docs/3.0.2/#fmi3SetContinuousStates) and §2.4.4, nominal defaults | Independent XML interpretation follows the ordered derivative entries to unique scalar continuous Float64 states, excluding dimensions, explicit nominal and declaredType. The actual metadata yields the compiled state and the same binary64 value as the output write. Arrays and inherited types require extensions of this judgment. |
| FMI 3.0.2 [§2.3.1, logging](https://fmi-standard.org/docs/3.0.2/#fmi3LogMessageCallback) | Both error messages and category storage are constructed from the actual table. Enabled execution retains every represented returning host effect or absent outcome; disabled execution is silent. Callback reentry, native divergence and writable host ownership retain the boundaries recorded below. |
| Actual C and header boundary | `AdapterContract` requires the complete nominal function contract; the fixed checker kernel-proves signature membership for the actual collected candidates. This does not prove header parsing, typedef/layout correspondence, ABI or native callback execution. |
| MLS 3.7 and eFMI 1.0.0 Beta 1 | No lexical, grammar, source initialization, GALEC/Solve, numerical or renderer changes. Existing clause maps and S01/SR07/SR08 findings carry forward. No additional production source case is admitted. |

All 33 added audit roots and affected packages pass in
`build/c-nominals/package-v2.log`. The required full `lake test` gate passed in
`build/c-nominals/full-gate.log`, including both actual archives and the existing
native, extraction and mutation checks. All 660 inventoried inputs remained
unchanged. Retained archives and hashes are in `build/c-nominals/artifacts/`
and `artifacts.log`; all C, header and GALEC members match `54618eb`.
No test suite is added. **Stage decision: open; grammar growth remains blocked.**

### All failure-helper outcomes: standards impact

This increment follows `7004a3e`; it changes proofs and mandatory artifact
contracts. The admitted subset, generated code and boundary checks are unchanged.

| Obligation | Coverage and boundary |
| --- | --- |
| FMI 3.0.2 [§2.3.1, logging](https://fmi-standard.org/docs/3.0.2/#fmi3LogMessageCallback) | Every represented returning host choice emits the evaluated environment/Error/category/message invocation, returns Error and preserves immutable strings. Disabled logging has empty events in the same machine. Existence and uniqueness of host outcomes are no longer premises of the mandatory helper contract. |
| FMI 3.0.2 [§2.2.1, callback restrictions](https://fmi-standard.org/docs/3.0.2/) | Log callbacks must not call back into the FMU. The atomic external relation does not model nested native execution; an admissible-host and native correspondence contract remains required. No-outcome stuck behavior is a property of this machine, not a claim about a native callback that never returns. |
| FMI 3.0.2 [§2.4.5, categories](https://fmi-standard.org/docs/3.0.2/#log-categories) | The same successful pool and actual XML category witness remain mandatory. Category selection through SetDebugLogging and all public-entry/lifecycle composition remain open. Writable host effects remain explicit, so private-instance framing still requires a host ownership contract. |
| MLS 3.7 and eFMI 1.0.0 Beta 1 | No changes to grammar, initialization, tensor/IR semantics, numeric policy or renderers. Existing clause maps and S01/SR07/SR08 findings carry forward; this does not expand the eFMI execution contract. |

Compiler composition passes in `build/c-logging-choices/promotion-v2.log`.
The 21 new roots retain every earlier audit root and axiom whitelist; affected
package checks pass in `build/c-logging-choices/package-audit.log`.
The required full artifact gate passed in
`build/c-logging-choices/full-gate.log`, with all 654 inputs unchanged and both
actual archives checked. Archives and hashes are retained in
`build/c-logging-choices/artifacts/`; their C, header and GALEC members match
`7004a3e` (`artifact-retention.log`). **Stage decision: open;
grammar growth remains blocked.**

### Eventful literal lowering: standards impact

This proof increment follows `d529b5d`. The admitted grammars, source/IR
semantics, renderers and tests are unchanged.

| Obligation | Coverage and boundary |
| --- | --- |
| FMI 3.0.2 [§2.3.1, callbacks](https://fmi-standard.org/docs/3.0.2/#fmi3LogMessageCallback) | Rechecked environment forwarding, callback parameters and string lifetime. The literal pass preserves all event labels, converted arguments and heaps; `logging_source` now carries this contract for its actual helper table. Native function-pointer correspondence and full public-call composition remain open. |
| Shared C transformation | Interface extension and literal replacement each have forward/reflected labeled simulations. Complete-call preservation derives structural premises from the actual function collection. Foreign effect relations are retained without a successful-outcome premise; execution inside a nonreturning foreign call is outside this machine. |
| MLS 3.7 and eFMI 1.0.0 Beta 1 | No grammar, initialization, numeric policy, DAE/GALEC/Solve or emitted-member change. The existing clause maps and S01/SR07/SR08 findings carry forward. This does not extend the eFMI execution contract. |

The actual checker requires the pass contract and successful pool preparation
alongside every earlier field. All 37 added audit roots and affected package
checks pass in `build/c-events/literal-package-audit-v1.log`. The required full
artifact gate passed in `build/c-literal-events/full-gate.log`, with all 651
inputs unchanged and both target archives checked. Their C, header and GALEC
members match `d529b5d`; artifacts and comparison evidence are retained in
`build/c-literal-events/`. **Stage decision: open; grammar growth remains blocked.**

### Enabled failure-helper callback: standards impact

This increment follows `c522107`. MLS 3.7 and eFMI 1.0.0 Beta 1 syntax,
initialization, tensor/IR products, numerical policy and emitted C/GALEC/XML
are unchanged. Existing S01/SR07/SR08 findings continue to block grammar growth.

| Obligation | Formal coverage and boundary |
| --- | --- |
| FMI 3.0.2 [§2.3.1, logMessage](https://fmi-standard.org/docs/3.0.2/#fmi3LogMessageCallback) | The actual enabled failure helper evaluates the stored environment and logger, passes Error/category/message, records the callback invocation and returns Error after the supplied host effect. Disabled logging retains the earlier proof. Arbitrary callback termination, reentrant hosts and full public-entry composition are not established. |
| FMI 3.0.2 [§2.4.5, log categories](https://fmi-standard.org/docs/3.0.2/#log-categories) | `logging_source` relates the constructed `logStatus` storage to the category in the actual model XML. Category and supplied immutable message bytes survive the call. Other SetDebugLogging/public lifecycle obligations remain separate. |
| C call and environment boundary | The scheduler, loop bodies, parameter conversion and continuations are shared. Symbolic function addresses and the callback prototype are explicit. Returning host effects must preserve read-only cells; their writable effects are retained. Identifier/field/index callee accesses are supported; function-designator dereference/casts, native ABI, allocation and nested external expressions are outside this increment. |
| Architecture and reuse | Generic labeled execution, finite/infinite histories, quiet embedding and label-preserving bisimulation live in core. backend-c owns callback dispatch and external semantics; backend-fmi3 owns the emitted helper contract. Existing literal-lowering/internal-call proofs are retained; eventful named-literal transformation was still an open bridge at this checkpoint. No new example suite or grammar case is added. |

The actual adapter checker now requires `Logging.FunctionContract` in addition
to every earlier field. All 58 new audit roots and affected packages pass
`build/c-events/package-audit-v1.log`. The required full artifact gate passed
in `build/c-events/full-gate.log`, with all 646 inventoried inputs unchanged
and both actual archives checked. Retained artifacts and hashes are in
`build/c-events/artifacts/`; their C, header and GALEC members match `c522107`
(`code-member-comparison.log`). **Stage decision: open; grammar growth remains
blocked.**

### Version call and XML agreement: standards impact

This increment follows `f9702f9`. Source syntax, initialization, lowering,
numerical policy, generated C/GALEC and XML renderers are unchanged.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| FMI 3.0.2 [§2.2.5](https://fmi-standard.org/docs/3.0.2/#fmi3GetVersion) | The version getter is permitted without an instance and in every interface state. The actual signature returns `const char *`. The mandatory function contract proves complete typed calls returning immutable, zero-terminated `3.0` storage from the collected pool, with an unchanged heap and no lifecycle/logging premise. The pinned header's `fmi3Version` macro is `3.0`; formal native macro/header and ABI interpretation remain open. |
| FMI 3.0.2 §§2.4.1, 2.4.10.1 | `version_source` relates that string to the version attributes in both actual XML documents. The model document is bound to prepared Solve; independent successful build decoding implies the required root/version fields. This is version agreement, not complete XML/FMI conformance. |
| MLS 3.7 and eFMI 1.0.0 Beta 1 | The admitted Modelica and GALEC grammars, equation semantics, initialization, IRs and emitted products are unchanged. Existing S01/SR07/SR08 findings and the full downstream gate remain applicable. |

No new example suite is added. All 11 new audit roots and affected packages pass
`build/fmi-version/package-audit.log`. The required full gate passed in
`build/fmi-version/full-gate.log`, with all 637
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-version/artifacts/`; their C and
GALEC members match `f9702f9` (`code-member-comparison.log`). **Stage decision:
open; grammar growth remains blocked.**

### ME count queries and complete metadata binding: standards impact

This increment follows `d147774`. The source EBNFs, LALR admission, IR lowering,
initialization, numerical policy, runtime C, metadata renderer and archive
layouts are unchanged. Two existing count getters instantiate reusable typed
call, lifecycle, printer, definition lookup and literal-pool proofs. No new
example suite or source case is introduced.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| FMI 3.0.2 [§2.3.2](https://fmi-standard.org/docs/3.0.2/#fmi3GetNumberOfContinuousStates) and §2.4.8 | Both count getters are ME-only; their initial counts sum the sizes of ModelStructure references. `CountMetadata.ScalarCounts` independently resolves each selected reference uniquely to a continuous scalar Float64, excludes dimensions and duplicate references, and counts those scalars. The current counts are one state and zero indicators. Structural parameters/array sizes are outside this admitted profile; extending the relation must interpret tensor volumes. This is a cardinality relation, not full XML/FMI conformance or a derivative/state graph proof. |
| FMI 3.0.2 §§2.3.1–2.3.2 and §2.3.8 | `CountQueries.FunctionContract` requires all terminating-call behaviors for success and null instances, plus lifecycle rejection and missing output with logging disabled. Rejected calls return Error and write Terminated. `counts_source` joins returned counts, Solve volume and actual metadata; `counts_failure_source` constructs the literal pool for the actual function list and preserves immutable bytes and the remaining heap. Enabled logger callbacks, allocation, ABI and other public calls remain open. |
| Actual metadata boundary | The earlier checker rejected a metadata mismatch natively, but its final theorem bound only public identifiers. `SourceBuildContract.metadata` now requires the full independent `XML.Document` relation on the same compiled artifact's prepared model. Candidate tree equality and actual bytes are kernel checked. The adapter contract additionally requires both count signatures/contracts and successful literal-pool construction; these are mandatory evidence, not optional helper theorems. |
| MLS 3.7 | Unit syntax, equations over Real, default initialization selection and source provenance are unchanged. The existing clause map and S01/SR08 findings carry forward. |
| eFMI 1.0.0 Beta 1 | The generic literal-install/load theorem is shared C infrastructure. Algorithm/Production Code, lowering and archive contracts are unchanged. Existing coding-guideline and SR07/SR08 findings carry forward; the downstream artifact gate remains required. |

The authored C dictionary, readable/writable instance cells, fresh symbolic
literal blocks and native preprocessing/header meanings remain explicit
boundaries. Success covers all allowed lifecycle modes; this is not a claim
of full public-API coverage. All 28 new roots and affected packages pass
`build/fmi-counts/package-audit-v2.log`. Elaborated quantifiers and interface
instances were inspected in `scope-review.log`; the constructed-pool theorem
has no supplied literal-address instance. The initial actual-file check stopped
at closed reduction of pool readiness. The candidate builder now composes
checked function-tree equalities and collection equations before kernel-checking
the explicit pool validity conditions (`pool-certificate-v13.log`). The required
proposition and axiom whitelist are unchanged. The strengthened actual-file
checker passes on the retained FMU in `actual-fmi-v2.log`. The required full gate
passed in `build/fmi-counts/full-gate.log`, with all 634
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-counts/artifacts/`; their C and
GALEC members match `d147774` (`code-member-comparison.log`). **Stage decision:
open; grammar growth remains blocked.**

### Complete FMI function-section grammar: standards impact

This increment follows `9751823`. Both source EBNFs, LALR admission, IR
lowering, initialization, runtime emission, metadata and archive layouts are
unchanged. The shared extension is a list-parametric C printer theorem and a
caller-parametric Lean candidate builder for signature spelling proofs. No new
runtime parser or example-based test suite is introduced.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| C11 [N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §§6.4–6.9.1 | `function_sequence_tokenization` composes independent function grammars, longest ordinary-code tokens and unchanged ordinary-string concatenation across actual function boundaries. Every existing FMI body and helper instantiates that theorem. Typedef spellings use an explicit name context; actual declarations, scope/type constraints and header/macro interpretation remain separate. The prior lexical/grammar clause review is reused without changes to those rules. |
| MLS 3.7 | All admitted/rejected forms, source equations, initialization selection, Real refinement and source spans are unchanged. The existing unit clause map and S01/SR08 findings carry forward. |
| FMI 3.0.2 ME/CS, [§§2.2.1–2.2.3](https://fmi-standard.org/docs/3.0.2/#header-files-and-naming-of-functions) | The actual `AdapterContract` requires the entire function-section grammar after its exact fixed preamble. The fixed checker kernel-checks spelling proofs for the header collector's 75 signatures. `adapter_reset_source` retains grammar and reset execution for the same definition list. The three official headers still define the API, types and prefix macros; the name-context grammar does not establish those meanings. Other public-call execution, allocation, callbacks and SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | No Algorithm/Production Code member, manifest, archive contract or method changes. The generic C theorem is reusable, but its composition with the actual eFMI C members is still required. Coding-guideline and SR07/SR08 findings carry forward. |

All nine new roots and affected packages pass
`build/fmi-functions/package-audit-v2.log`. The fixed actual-file checker passes
in `build/fmi-functions/actual-fmi.log`. The required full gate passed in
`build/fmi-functions/full-gate.log`, with all 625 inventoried inputs unchanged
and both actual archives checked. Exact archives and hashes are retained in
`build/fmi-functions/artifacts/`; their C/header/GALEC members match `9751823`.
The type-coverage review found 57 of 75 collected signatures with an adjusted
parameter spelling absent from `FMI3.cTypes` (43 spellings). The universal
count-getter result confirms a concrete entry failure in the authored typed
machine, while native C checks pass. This sharpens the existing F03/SR07
proof-coverage finding; it is not a new native standards failure. See
`build/fmi-functions/signature-types.log` and `unmapped-call-v2.log`.
**Stage decision: open; grammar growth remains blocked.**

### C maximal tokenization and concatenation: standards impact

This increment follows `3497310` and changes proof relations and the required
reset artifact contract. Both source EBNFs, parser/lowering behavior, emitted
C bytes, numeric initialization, metadata and archive layouts are unchanged.
The shared mechanism is a suffix-parametric refinement of token judgments,
followed by grammar induction. It adds no runtime scanning or parsing pass.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| C11 [N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §6.4p4 and §§6.4.2–6.4.8 | `CTokens.Normal.Candidate` covers the ordinary-code competing token classes, including conservative universal-name/nonbasic extensions and encoded/character literal prefixes. `Consumes.normal` proves longest matching across those classes with the actual continuation. Header names belong to include/implementation-defined pragma contexts, which remain excluded. The enlarged candidate envelopes are not output acceptance rules or a claim that every candidate is valid on a host. |
| N1570 §6.4.9 | Per-class no-comment theorems exclude both comment openers at actual token starts. Literal payload slash/star characters are preserved inside independently decoded strings. This is a comment-free printed subset, not a general comment reader. |
| N1570 §§5.1.1.2 and 6.4.5p5–6 | Shared expression/statement/function grammar proofs separate ordinary literal tokens. `FunctionDenotes.tokenization` uses one witness for maximal lexing, the intended function tree and stability under concatenation. Tokens retain object bytes, anticipating the phase-seven terminator; joining removes the intermediate terminator. Prior macro expansion, source/execution encodings and header interpretation remain separate. |
| MLS 3.7 | No source admission, equation, initialization, Real refinement or diagnostic change. The existing clause map and S01/SR08 findings carry forward. |
| FMI 3.0.2 ME/CS | `Reset.FunctionContract.tokenization` is now required by the actual adapter certificate alongside all earlier fields. `adapter_reset_tokenization` locates its exact fragment. Other functions, headers, allocation, callbacks and SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | The reusable C theorem is available to Production Code. This increment does not change the eFMI file/archive proposition, GALEC, manifests or methods, and does not close coding-guideline or SR07/SR08 obligations. |

All 67 new roots and affected packages pass
`build/c-lexical/composed-audit.log` (2460 jobs), with the existing axiom
whitelist. The required full `lake test` gate passed in
`build/c-lexical/full-gate.log`, with all 621 inventoried inputs unchanged and
both actual archives checked. Exact artifacts and SHA-256 identities are in
`build/c-lexical/artifacts/`. No new example-based suite was added.
**Stage decision: open; grammar growth remains blocked.**

### Shared C token and function grammar: standards impact

This increment follows `95cb4bc` and keeps the production subset and both EBNF
files unchanged. It adds shared proof rules and strengthens the actual reset
artifact contract; it changes no IR semantics, initialization, generated C,
FMI metadata, GALEC or archive layout.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| C11 [N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §§5.2.1 and 6.4.2–6.4.8 | Independent identifier, preprocessing-number, ordinary-string and all-punctuator candidate rules support actual-suffix lexical composition. Word rules include universal-name syntax and conservative nonbasic extensions. Cross-category longest matching, valid implementation extensions and phase-six string concatenation remain open. |
| N1570 §§6.5, 6.7, 6.8 and 6.9.1 | Shared printer theorems preserve the intended expression precedence, initializer/assignment categories, compound control bodies, parameter lists and static/external definitions. Raw type strings require explicit `TypeDenotation`. C type constraints, scope, macros, header declarations and ABI interpretation are separate. |
| MLS 3.7 | Admission, equation and initialization semantics, Real refinement and diagnostics are unchanged. S01/SR08 remain open as recorded in the unit review below. |
| FMI 3.0.2 ME/CS | `Reset.FunctionContract` adds the shared text/tree judgment while retaining all existing call and memory guarantees. `adapter_reset_syntax` binds it to the actual adapter fragment. Other calls, whole-file interpretation and SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | Shared C proof infrastructure is available to Production Code; no eFMI printer or artifact proposition is changed by this increment. Existing GALEC, Production Code, manifest and coding-guideline findings carry forward. |

All 85 new roots and affected packages pass
`build/c-token/final-package-audit.log`. The required full `lake test` artifact
gate passed in `build/c-token/full-gate.log`, with all 613 inventoried inputs
unchanged. Exact checked FMU/eFMU archives and their SHA-256 identities are
retained in `build/c-token/artifacts/`. No new example-based suite is added.
**Stage decision: open; grammar growth remains blocked.**

### Prior unit-stage baseline

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
| MLS A.2.1, A.2.2, A.2.4, A.2.6–A.2.7: one model, declaration and equality equation. [Concrete syntax](https://specification.modelica.org/maint/3.7/modelica-concrete-syntax.html) | [ParserProofs](../packages/modelica-parser/ModelicaParser/ParserProofs.lean): `parsed_in_ebnf`; [Compiler](../packages/compiler/Rumoca/Compiler.lean): `compile_complete` for the resolved unit token shape. | Generated-grammar membership and independent metalanguage correspondence are proved for the admitted dialect (P02). S01 retains correspondence with MLS; there is no full MLS parser-completeness claim. |
| MLS §§8.2–8.3.1: equation lookup and compatible equality operands. [Equation clauses](https://specification.modelica.org/maint/3.7/equations.html) | [AST](../packages/modelica-parser/ModelicaParser/AST.lean): `Resolved`; [LocatedProofs](../packages/modelica-parser/ModelicaParser/LocatedProofs.lean): `resolved_references`, `resolve_error_locations`. | The derivative must name the one declared state; failed resolution has exact occurrence/declaration spans. General scopes are excluded. Record the literal-Integer-to-Real interpretation explicitly in S01. |
| MLS Operator 3.12: `der` is the time derivative of the continuous Real operand. [Operator clause](https://specification.modelica.org/maint/3.7/operators-and-expressions.html) | [Source](../packages/compiler/Rumoca/Source.lean): `Solves`, `trajectory_derivative`; [Behavioral](../packages/compiler/Rumoca/Behavioral.lean): `lowering_chain_behavior_correct`. | The ideal `x₀ + t` trajectory and unit derivative are proved. This does not give finite storage semantics or choose an initial value. |
| MLS §4.9.1: finite stored Real values. [Real type](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html) | [Encoding](../packages/core/RumocaCore/Real/Encoding.lean): `finiteEncodingEquiv`; [Verified](../packages/compiler/Rumoca/Verified.lean): `compiler_semantic_preservation` and `ArtifactContract.real_solution_refinement`. | Binary64 profile and rounding refinement are proved under the documented C/IEEE assumptions. S01/N01 still require reviewed correspondence; unbounded mathematical trajectories are not stored Real values. |
| MLS §8.6 and §4.9: initialization and fallback selection; FMI initialization metadata; eFMI Startup. | Source takes an external finite initial value; [FMI metadata](../packages/backend-fmi3/RumocaFMI3/Metadata.lean) supplies a zero start; [GALEC](../packages/core/RumocaCore/GALEC/IR.lean) selects zero in Startup. | **Open SR08/S01:** justify and compose these policies, including any required diagnostic. Do not infer an initial equation from the derivative equation. |
| FMI §§2.3–2.5, Chapters 3–4: common lifecycle, ME/CS, metadata and artifacts. [FMI specification](https://fmi-standard.org/docs/3.0.2/) | Existing [FMI contracts](fmi3/contracts.md), source-build certificate and selected public-call theorems. | SR01–SR02 corrections are checked. SR04–SR05 and SR07 remain open; selected calls and numerical-file proofs do not certify the complete adapter/archive. |
| eFMI Chapters 2, 3 and 5: container, Algorithm Code and Production Code. [Beta 1 specification](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip) | [EFMIArchiveProofs](../packages/compiler/Rumoca/EFMIArchiveProofs.lean): `compile_archive_verified`, retaining code, method, mapping and manifest contracts. | SR03's status correction is checked. SR06 is resolved as the documented checker limitation below; SR07 and the SR08 cross-standard initialization review remain open. |

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

### Independent EBNF reader: standards impact

This candidate follows `e9f41c7`. The Modelica and GALEC EBNF hashes still match
the unit-stage table above. No source production, lexer policy, initialization,
IR lowering, numerical behavior, interface or archive layout changes.

| Baseline | Change and claim boundary |
| --- | --- |
| MLS 3.7 §§2 and A.2 | Independent character/token relations now specify the existing EBNF dialect. The public reader is sound and complete at its normal budgets; generated Modelica source contracts compose this notation with EBNF-to-CFG preservation and LALR acceptance. This closes a reader-proof gap after integration; it does not assert full MLS grammar coverage or settle S01/SR08. |
| FMI 3.0.2 ME/CS | The existing source profile, Solve preparation, emitted C and interface contracts are unchanged. The same complete artifact gate remains required. Open adapter/lifecycle and standards findings carry forward. |
| eFMI 1.0.0 Beta 1 | The same independent notation theorem is emitted for GALEC. The admitted GALEC block, Production C path and archive contract are unchanged. A proof of this documented EBNF dialect is not a full ISO 14977 or eFMI conformance claim. |

Forty generic roots pass the parser package audit in
`build/source-cutover/build/ebnf-reader/parser-package.log`; both grammars were
regenerated. Both language package audits and the existing integration checks
pass in that directory's `language-packages.log` and `integration.log`.
The required main artifact gate passed in `build/ebnf-reader/full-gate.log`,
with all 591 inventoried inputs unchanged and both actual target archives
retained under its `artifacts/` directory. This closes P02 for the documented
notation; it does not complete correspondence with the prose standards.
No new test suite or grammar case is introduced. Stage decision stays open:
the remaining core, adapter and standards obligations still block growth.

Earlier checkpoint entries below describe P02 as open at those checkpoints.
The reader increment above closes it; their other standards findings remain open.

### Generic C character-preservation increment: standards impact

The admitted Modelica/GALEC productions, Solve programs, generated C and
FMI/eFMI artifacts are unchanged. This increment strengthens the actual FMI
adapter contract with a reusable theorem about character rewrites.

| Standard | Coverage and remaining boundary |
| --- | --- |
| [C11 N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §§5.1.1.2 and 5.2.1.1 | Generic CTree fragments and the complete FMI adapter are stable under trigraph replacement and physical newline splicing. Raw name/type conditions are explicit and checked. Encoding, preprocessing tokens, macros, headers, typing and execution are separate. |
| MLS 3.7 | Source-name safety follows from the existing lexical theorem. Grammar admission, equations and initialization are unchanged; S01/SR08 remain open. |
| FMI 3.0.2 ME/CS | The actual-file contract includes the new character property while retaining its byte identity and reset behavior. Other public-call, allocation/callback, header/ABI and full artifact obligations remain open. |
| eFMI 1.0.0 Beta 1 | Shared CTree theorems are available to the backend. GALEC/Production Code methods, manifests and packaging are unchanged. No new eFMI conformance claim is made. |

All 35 new roots pass the unchanged axiom policy and affected-package audits
in `build/source-cutover/build/c-printer/composed-package-audit.log`. The fixed
checker passed on the retained FMU files in `actual-fmi.log` in that directory.
The required main artifact gate passed in `build/c-printer/full-gate.log`, with
all 596 inventoried inputs unchanged and both actual archives checked. Exact
archives and hashes are retained in `build/c-printer/artifacts/`.
This is partial assurance progress; the remaining findings still block growth.

### C literal-printer increment: standards impact

The subsequent shared-printer correction is tracked under C01/F03 in
[the roadmap](roadmap.md). It escapes question marks and proves exact literal
bytes after the selected C11 preprocessing rewrites. MLS source admission,
resolution, equation semantics and both EBNFs are unchanged. The FMI impact is
its emitted literals for version/token/category/error handling; correct literal
printing is a prerequisite for complete call proofs, not their replacement.
The current eFMI Production C profile contains no string expressions; its
GALEC method, mapping and initialization obligations remain the same.

The C package audit and disposable native reproduction pass. The complete local
gate for `a0327a1785b50d9cc4b10e4ce29134fc27cc632b` passed in
`build/c-string-printer-full-gate.log`, including both artifact paths. The log
now records their SHA-256 identities:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `0d27780b6d2e67f8e68be8157edb0ef52aa564d97e4032e50b63687841ba488a` |
| `build/Integrator.efmu` | `31315a9ec8fc006e9e7c515bec6ae926a8f822fb51a175784ebd218504479886` |

The [hosted run for this revision](https://github.com/CogniPilot/rumoca_lean/actions/runs/34527453846)
also passed. The earlier snapshot's artifact hashes must not be reused for
this run. No SR04–SR08
or whole-adapter obligation is closed by the literal theorem, and this is not
a new completed spiral stage.

### C literal-storage increment: standards impact

The C01/F03 increment adds typed character storage and universal
read-only preservation proofs. It does not change the emitted production C,
source admission, either EBNF, MLS equation/initialization semantics, FMI
metadata/lifecycle policy or eFMI GALEC/Production Code policy. It is a
prerequisite for modeling the FMI adapter's real string-pointer arguments.
The existing clause map and its open findings therefore remain applicable.

The selected C profile uses eight-bit unsigned or two's-complement signed
characters; it does not cover every implementation allowed by
[C11 N1570 §§6.2.5–6.2.6](https://www9.open-std.org/JTC1/SC22/WG14/www/docs/n1570.pdf).
The representation proofs reuse Std, and integer-to-character conversion
accepts only in-range values. Section 6.4.5's literal array bytes are related
to loads from supplied read-only objects, with a fresh-block construction to
establish that the storage premise can be satisfied. No address-distinctness
claim is made for different literal texts; §6.4.5 permits storage sharing.
Actual global storage, static lifetime, array-to-pointer decay and callback
interaction remain unproved. Native character-profile validation is also an
external obligation, not a consequence of the byte round-trip theorem.

The nine new theorem roots pass `build/c-literal-storage-audit.log` with the
unchanged axiom whitelist. The required complete gate passed in
`build/c-literal-storage-full-gate.log`, including the actual archive theorem,
independent extraction, schemas, native execution and mutation controls.
The log records this run's retained artifacts:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `7dc758358ee5f5a253147d4095bef525732b69f4996714fc582e406306620ac3` |
| `build/Integrator.efmu` | `ee10eada0dfb93e153a90375f09da7e5d68bc9c611fb99456ea96ce0a63188e8` |

These identities supersede the preceding snapshot for this run. **Stage decision: open.**
This increment does not close any existing compliance finding or authorize
grammar growth.
The [hosted run for 1bbafeb](https://github.com/CogniPilot/rumoca_lean/actions/runs/34533601963)
also passed.

### C literal-pointer and rejected-call increment: standards impact

Reviewed checkpoint: `f3ad41dac6b150bff03b79fbdf5ab76f8bde82fe`.

The next SR04/C01/F03 increment replaces abstract C string values with an
explicit literal-address map, typed pointer conversion and a storage/printing
bridge. `ErrorCalls.nominal_reject_correct` covers the complete generated
nominal-query call from Instantiated through its failure helper and ordinary
return when logging is disabled. It returns Error, sets Terminated and frames
every cell outside the mode field. Counts range over all UInt64 values; output
pointers may be null because the rejection precedes their dereference.
The declaration matches the pinned `fmi3FunctionTypes.h` signature. The added
`fmi3String` alias follows `fmi3PlatformTypes.h`'s const-character pointer.

The applicable FMI status and lifecycle clauses are the same ones reviewed in
SR04 below. The theorem checks the corrected rejection's execution; enabled
callbacks and binding the complete actual adapter bytes remain open. The C
profile selects one address per literal text. Its supplied storage contract
allows compatible sharing, but does not prove every permitted per-occurrence
allocation or the native compiler's global setup. Do not infer those facts
from byte preservation or a function-tree call theorem.

The next callback contract must also retain FMI's logging controls:
[`loggingOn = false` disables callbacks](https://fmi-standard.org/docs/3.0.2/#fmi3InstantiateModelExchange),
and [§2.2.1 forbids the logger from calling back into the FMU](https://fmi-standard.org/docs/3.0.2/#general-mechanisms).
Enabled logging still needs an explicit request/return and memory-effect
contract; assuming that an arbitrary callback simply succeeds would not
establish it.

MLS admission, both EBNFs, initialization/numerical policy and emitted C are
unchanged. The eFMI profile emits no string expressions and keeps its existing
GALEC, Production C and manifest contracts. SR05–SR08 remain open. Twelve new
roots and all affected package audits pass in
`build/c-literal-call-package-audit.log`. The required full local gate passed in
`build/c-literal-call-full-gate.log`, including both FMI interfaces, the complete
actual eFMU archive certificate, independent extraction, schemas, native C and
mutation controls. Both EBNF identities still match the unit-stage table above.
This run retained the following artifacts:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `e1dc2271f9fa22ed5454eb5e30908e26d59bcd41d5231ccdc53bb94f85dc03c7` |
| `build/Integrator.efmu` | `dd22dca1dac2f3af228a3f8bc79e9934ba20860f583daa5a7892654c74d6fb88` |

These hashes identify this increment's local artifacts, not those from its
preceding storage checkpoint. **Stage decision: open; grammar growth remains
blocked.** The new function-tree proof is not a whole-adapter certificate.
The [hosted run for f3ad41d](https://github.com/CogniPilot/rumoca_lean/actions/runs/34536535660)
also passed.

### Named string-storage preparation: standards impact

The next C01/F03 increment prepares a string-expression-to-data-name lowering.
Its memory-body theorem preserves all observations, including failure and
divergence, under explicit binding and freshness conditions. It does not yet
emit static-array declarations or replace the production renderer. Actual
global storage, typed calls, enabled callbacks and complete adapter binding
remain open. The theorem is about the authored C machine; it is not evidence
that the native compiler uses the selected literal-address map.

MLS admission, both EBNFs, initialization and numerical policy, FMI metadata
and lifecycle, and eFMI GALEC/Production Code and manifests are unchanged.
The current clause map and SR04–SR08 findings therefore carry forward. The
core/C package audit passed in `build/c-literal-lowering-package-audit.log`,
including all seven new audit roots under the unchanged whitelist. The required
full local gate passed in `build/c-literal-lowering-full-gate.log`, including
both FMI interfaces, the actual eFMU archive certificate, extracted manifests,
schemas, native C and mutation controls. The retained artifacts are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `a83b4c29e60867fa69052c5dd3ccf10bd46004fb22e41fadd8b294b027155d3d` |
| `build/Integrator.efmu` | `4c2e2bb0693280dc3dafb66441d444bbb9e023053a6334ed7145c70436eb5657` |

**Stage decision: open.** This preparation does not close actual global storage,
the whole adapter or any existing compliance finding.
The [hosted run for 9ea13be](https://github.com/CogniPilot/rumoca_lean/actions/runs/34539932871)
also passed.

### Typed loop/call string-storage preparation: standards impact

This increment extends the previous lowering proof to typed loops and ordinary
calls, including recursive calls, failed execution and divergence. The public
entry theorem derives the empty continuation invariant. Supplied global-name
bindings and structural freshness remain premises; the proof compares machines
using the same interface and does not yet construct the actual global pool or
certify insertion of declarations into the emitted C translation unit.

| Standard | Review of this increment |
| --- | --- |
| MLS 3.7 | Source admission, both EBNFs, equation/initialization semantics and numeric policy are unchanged. The existing clause map, P02 and SR08/S01 carry forward. No development profile enters production. |
| FMI 3.0.2 ME/CS | Runtime C, metadata, lifecycle, errors/logging and archive contents are unchanged by this proof pass. SR04 still needs enabled callback and complete adapter/global-storage coverage; SR05 and SR07 remain open. |
| eFMI 1.0.0 Beta 1 | GALEC methods, prepared Solve program, Production C, logical mappings, manifests and packaging are unchanged. The layout review below resolves SR06 as a checker limitation. SR07's release obligations and SR08's initialization correspondence remain open. |

The thirteen new roots pass the unchanged axiom whitelist in
`build/c-literal-loop-call-package-audit.log`. The required full gate passed
in `build/c-literal-loop-call-full-gate.log`, including both FMI interfaces,
the exact eFMU archive theorem, official schemas/checksums, native C and mutation
controls. No unit tests or source cases were added. Both EBNF hashes above
were rechecked and are unchanged. The retained artifact identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `4d3121d6cb44cd908ee3dc68e88fd2784f11137accee96d070c2995dbbb1436c` |
| `build/Integrator.efmu` | `7e2a6d7587706337e8d45ebf386ba28582ee9ce0a1dbcfcc13010dd2aa937777` |

**Stage decision: open; grammar expansion remains blocked.** The new theorem
closes the conditional loop/call lowering obligation, not the actual global
setup or complete compiler chain. SR04, SR05, SR07 and SR08 remain open; SR06's
separate disposition resolves only the standalone packaging question.
The [hosted run for 6be8fb6](https://github.com/CogniPilot/rumoca_lean/actions/runs/34543106088)
also passed.

### Checked literal pool and interface extension: standards impact

This increment constructs a validated symbolic string pool and proves that
adding its data bindings preserves the original program's identifier lookups.
`CLiteral.Pool.invocation_behaviors` composes this result with the earlier
literal lowering for every typed-call observation, including failure and
divergence. The storage theorem constructs immutable objects; fresh blocks
preserve existing cells. It does not emit declarations or change production C.

| Standard | Review of this increment |
| --- | --- |
| MLS 3.7 | The frontend, both EBNFs, IR lowerings, equation/initialization meaning and numerical profile are unchanged. The existing clause map, P02 and SR08/S01 carry forward. The EBNF hashes above were rechecked; no development case enters production. |
| FMI 3.0.2 ME/CS | Runtime C, headers, metadata, lifecycle and packaging are unchanged. This prepares explicit string storage for the adapter; it does not close logging, public-call, header/linkage or actual-adapter obligations. SR04, SR05 and SR07 remain open. |
| eFMI 1.0.0 Beta 1 | GALEC, prepared Solve, Production C, mappings and manifests are unchanged. The official specification archive still matches the pinned hash. The eFMI resources page still lists Beta 1 as a release candidate; SR06 retains its documented checker limitation. SR07 and SR08 remain open. |

The symbolic construction uses separate block slots; it makes no native C
layout or allocation claim. A future declaration printer must establish the
selected C storage, lifetime and array-decay rules and its complete emitted
bytes. The existing C11 correspondence obligations remain applicable. Source
name collection alone does not validate arbitrary header macros or typedefs.

All 27 new roots pass the unchanged C package axiom audit in
`build/c-literal-pool-package-audit.log`. Review of the elaborated signatures
caught an implicit `reserved` identifier resolving to the imported Modelica
keyword list. Explicit parameters now make the pool results general over
reserved-name lists. The interrupted gate was discarded; the corrected source
passed the required full local gate in `build/c-literal-pool-full-gate.log`,
including the actual eFMU theorem, FMI ME/CS checks, official schemas/checksums,
native C and mutation controls. Reviewed artifact identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `457f8f5b5a59b368054923a4637ff0fd190bda65096541d29da9d0d7009156ca` |
| `build/Integrator.efmu` | `c3fde89246c37fe7448f56bdedb757d9f8a2b6e82692a73bfa814c1106955915` |

No new unit tests or source cases were added.
**Stage decision: open; grammar expansion remains blocked.**

### Literal declarations and FMI function binding: standards impact

This increment supplies an independent declaration-list grammar and proves
exact ordered names and initializer bytes, then connects them to the checked
pool's constructed symbolic storage. It collects literals from every tree
constructor and applies the pass to the actual FMI renderer's function list.
The constructed definition table derives helper bindings and tree coverage;
the authored constant exclusions and structural call conditions are proved.
The complete observation-equivalence theorem includes returns, failure and
divergence. The production C emitter, metadata and package layout are unchanged
by this preparation.

| Standard | Review of this increment |
| --- | --- |
| C11 N1570 §§5.1.1.2, 6.7.9 paragraphs 14/22 | Independent syntax models static character arrays with bounds supplied by their literal initializers, including the terminator. The complete-block proof excludes trigraph/splice changes across physical declaration lines. Macro expansion, the surrounding translation unit and native allocation/layout are separate. |
| C11 N1570 §§5.2.4.1, 7.1.3 | Actual `Pool.make` names start with `rumoca_literal_`, satisfy the checked 63-character bound and exclude supplied names. This does not validate all implementation macros/types or arbitrary `Pool.check` inputs. |
| MLS 3.7 | EBNFs, frontend, IR lowering, source equations and numerical admission are unchanged. P02 and SR08/S01 remain open. |
| FMI 3.0.2 ME/CS | The proof now uses the actual rendered function list, but is not a complete adapter-file or public-call certificate. Unsupported external calls still have stuck observations in the authored machine. Enabled callbacks, header/ABI and allocation remain open; SR04, SR05 and SR07 are not closed. |
| eFMI 1.0.0 Beta 1 | Shared C preparation is available to either backend; GALEC, Production C and packaging are unchanged. SR06's standalone-layout disposition and SR07/SR08 remain as recorded. |

The C clause review uses the [official N1570 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
All 34 new shared C/FMI roots passed with the unchanged axiom whitelist in
`build/c-literal-declarations/package-audit.log`. The full required
`nix develop .#verification --command lake test` gate passed in
`build/c-literal-declarations/full-gate.log`, including both FMI interfaces,
the actual eFMU theorem, extraction, official schemas/checksums, native C and
mutation controls. The checked source snapshot still matches
`build/c-literal-declarations/source.sha256`. Artifact identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `30e39977357de58364f4a2a6d1a3dbf4813b4b1ea950c46cf4197c6b7dc47d29` |
| `build/Integrator.efmu` | `22b0750229afa80eb3986e3076587ba3965cd40d37fbcd4cdc1c04dc4c92004d` |

No new unit tests or language cases are added.
**Stage decision: open; grammar expansion remains blocked.**

### Adapter call and lexical preparation: standards impact

This increment derives the instantiated nominal-query rejection from the
actual collected literal pool and renderer's function table, with disabled
logging. It also proves successful header reads have unique function names.
The production renderer does not yet invoke the literal pass. Its signature
membership, helper/public name separation, callbacks and full-file binding
remain open.

| Standard | Review of this increment |
| --- | --- |
| C11 N1570 §6.4 paragraph 4 and §6.4.6 | The shared scanner prefers a matching configured pair to a single symbol. Exact whole-result refinement, including errors and offsets, holds for all prior disjoint configurations. The new C configuration is a restricted lexical prerequisite, not a complete preprocessing-token grammar. |
| C11 N1570 §6.4.4.1 | The numeric theorem uses a single zero or a nonzero leading digit and independently computes the base-10 value. It excludes leading-zero octal ambiguity. C integer type selection and representability still need their own contract. |
| MLS 3.7 | Source EBNFs, source semantics and production admission are unchanged; P02 and SR08/S01 remain open. |
| FMI 3.0.2 ME/CS | The rejection theorem covers either interface kind and arbitrary nominal output pointers/counts, but only the Instantiated state with logging disabled. It preserves literal bytes and all heap cells except mode. It does not close SR04/SR05/SR07 or establish complete FMI execution. |
| eFMI 1.0.0 Beta 1 | GALEC and Production C scanner configurations have proofs of exact result/error preservation. The source profiles, manifests, methods and packaging are unchanged. SR07/SR08 remain open. |

The C clauses were checked against the [official N1570 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
The existing package audits include 17 new roots; no test suite or source case
is added. The required `nix develop .#verification --command lake test` passed
in `build/adapter-preparation/full-gate.log`. The package source snapshot in
`build/adapter-preparation/source.sha256` was checked unchanged after the gate.
The resulting artifact identities are:

| Artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `dbbe7b470a7cfeeb6bf11d522cd95705ad0d10bab8c40d80eeba62dbfa7b8c32` |
| `build/Integrator.efmu` | `b9326e66377399c8228fd01a35107e01b9760f5c0239f8b2945c5caa7b1f597a` |

This checks the preceding production artifacts; initialization work remains
isolated and is not covered by this gate. The partial adapter theorems do not
establish the remaining whole-adapter contract.

**Stage decision: open; grammar expansion remains blocked.**

### Mandatory located source: standards impact

The production artifact now requires its checked located parse. The driver
returns source-indexed diagnostics directly, and the CLI no longer reparses
failures. Generic exact-spelling attachment completeness is derived using
Lean's UTF-8 cursor and iterator proofs. The actual Modelica lexer discharges
the spelling contract, and `compile_complete` retains its original lexical
and resolution assumptions. Invalid-source diagnostics may gain precise
locations; the admitted source syntax and numerical behavior are unchanged.

| Standard | Review of this increment |
| --- | --- |
| MLS 3.7 lexical and concrete-syntax profile | No EBNF production, token class or name-resolution rule changes. The completeness theorem covers the same independent lexer/AST specification, without assuming attachment success. Generic UTF-8 cursor proofs do not enlarge the admitted identifier language. SR08/S01 initialization remains open. |
| FMI 3.0.2 ME/CS | Numerical Solve/C, adapter bodies, metadata and packaging are unchanged. Artifact certificates now construct mandatory source locations using the proved total frontend. This is source provenance, not an emitted-code map or a new FMI lifecycle guarantee. SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | GALEC/Production C and manifest generation are unchanged. Their actual-file certificate generators use the located compiler theorem. GALEC IR origin propagation and actual emitted-byte source maps remain open with SR07/SR08. |

Fourteen new roots are registered in the existing audits. The package gate
passed in `build/located-provenance/package-gate.log`; the required full gate
passed in `build/located-provenance/full-gate.log`, including actual numerical
C and GALEC certificates, independent FMI ME/CS import, and checked eFMU
publication, schemas, native execution and mutation controls. The unchanged
package source snapshot was checked against
`build/located-provenance/source.sha256` after completion. Artifact identities:

| Artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `169c5964757a1faf7abd08e933b7efc96c700cc98bb03fed459a730fd37e0005` |
| `build/Integrator.efmu` | `472993590dd53d9cb3f1365f746563696ca5d0fee7567786790c7f235e55124b` |

Initialization preparation remains in the isolated checkout and is excluded
from this production gate. These results do not close the remaining provenance
or standards findings.

**Stage decision: open; grammar expansion remains blocked.**

### Shared source origins: standards impact

The generic engine now provides checked source/derived/generated origin tables,
with mandatory parent/rule records and ancestry preservation. The Modelica
frontend supplies exact field and production ranges for its existing AST; the
GALEC lexer supplies the generic attachment-completeness contract. The parallel
frontend reuses the shared immutable input record without changing scheduling
or analysis results.

| Standard | Review of this increment |
| --- | --- |
| MLS 3.7 | The same fixed lexical/AST profile is admitted. Token-indexed production boundaries and literal/name text are proved for the actual parse. No declaration, binding, modifier, initialization, tensor or AD syntax is added. SR08/S01 remains open. |
| FMI 3.0.2 ME/CS | Solve, C, adapter bodies and FMI metadata are unchanged. Source-origin tables are not a lifecycle theorem or a printer map. SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | Exact source attachment is proved for the current GALEC scanner. Required GALEC IR origins, generated-member maps, and initialization correspondence remain open. Algorithm/Production Code emission is unchanged. |

Twenty-three new roots pass the existing package audits in
`build/origin-tables/package-gate.log`; the required full artifact gate passed
in `build/origin-tables/full-gate.log`. It includes actual numerical C and GALEC
certificates, independent FMI ME/CS import, and checked eFMU publication,
schemas, native execution and mutation controls. The package inventory in
`build/origin-tables/source.sha256` was checked unchanged after completion.

| Artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `4f967951f8e730aa11826d230c906237d96209d56cec0c8214a7bfa8b6c15b05` |
| `build/Integrator.efmu` | `c84a3797dc25ab9a754c631b92488209f09701f9f13b500021952f6df167031e` |

The checked graph prevents absent/dangling parents, but compiler-specific rule
correctness and per-IR occurrence coverage still require their own proofs.

**Stage decision: open; grammar expansion remains blocked.**

### Scoped initialization and required IR origins: standards impact

The unmodified Real/unit-derivative production grammar and both EBNF identities
above are unchanged. The integrated initialization/provenance implementation
was prepared in `build/literal-call-worktree`. Its full gate passed in
`build/scoped-full-gate.log`, and `build/scoped-sources.sha256` remained unchanged
throughout that run. The current mainline audit roots are all retained; older
worktree audit lists were reviewed and restored before integration.

| Normative obligation | Checked correspondence | Open boundary |
| --- | --- | --- |
| MLS 3.7 §§4.4.2.1, 4.9 and 8.6: bindings, start guesses, fallback and selected initial conditions. | `Initialization.Real` proves preparation soundness/completeness, constant-binding inconsistency for `der(x)=1`, and a unique completed trajectory. `Source.initializes_iff` retains the unfixed source equation. Required Flat/DAE/Solve settings select zero with both notices, whose declaration spans agree between compiler and LSP. | No binding/start/fixed syntax is admitted. General initialization systems remain outside this grammar. |
| FMI 3.0.2 §§2.3.1–2.3.3: instantiated defaults, host changes, initialization and reset. | Prepared Solve data supplies an explicit C store after allocation and on reset. `CInitialization.write_behaviors` proves its value and heap frame; existing body/literal-call proofs cover that statement. The full isolated gate passes both ME and CS boundaries. | Allocation, public-call/artifact composition and the SR04/SR05 lifecycle and host-set policy remain open. |
| eFMI 1.0.0 Beta 1 §3.2.3, §3 R-1: Startup determines block-variable initialization. | Existing actual Production C contracts initialize state, period and status from writable uninitialized storage. `GALEC.initialization_matches` identifies the same selected source plan. The added `ArchiveStartupContract` binds the actual C member, all terminating Startup behavior, the value read from the resulting heap, and the completed source solution. Its strengthened actual-file proposition passed the final integrated gate below. | GALEC/Solve operation origins, manifest/source-map correspondence and general coding-guideline obligations remain open. |

Artifact identities for the completed **isolated preceding snapshot**, not the
subsequent strengthened checker or the main workspace's later artifacts:

| Artifact in the isolated checkout | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `c6c4b6dcddcbe0bcef6f53307c24dc3fbe7367798f3b7a09811097c46fd6901a` |
| `build/Integrator.efmu` | `d08885b29e3c9886fc278b19de2cb22e58114888c8864d3f23fb9492c20db3fa` |

The added archive-initialization roots and affected package audits pass in
`build/literal-call-worktree/build/scoped-startup-integration.log`. Main-workspace
package/audit checks passed in `build/initialization-provenance/package-gate.log`
(3282 jobs), retaining all 1108 prior audit entries and adding 50. Its final
full gate passed in `build/initialization-provenance/full-gate.log`, including
the strengthened actual-file proposition. The main-workspace input inventory
`build/initialization-provenance/sources.sha256` was unchanged after completion.
Its final retained artifact identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `df945b602bf305b402cc361f86c41d85fa7afa86eed6e111e5dd9c80ec482a54` |
| `build/Integrator.efmu` | `eb403ed61b99b92d914e4a00e3ff8e98ef938469eb8d51b4ac6f794e5ccc2e2c` |

Fixed source-file certificates now quote the actual checked filename and bytes
together. `Artifact.source_identity` preserves the caller's complete input table
and selected entry. Published checks name their staged snapshot; no certified
map to the original filename or generated archive-member ranges is claimed.

The neighboring Rust checkout was read at `bc71577f85df24957e5c9ab30fdaf4ed48da4311`
with user changes present. Its provenance and initialization ownership informed
the review; no Rust file was modified. Inspected file identities are retained in
`build/literal-call-worktree/build/scoped-rust-reference.sha256`. The normative
authorities remain the pinned standards linked above.

**Stage decision: open.** SR08, PV06–PV09 and the whole-adapter obligations still
block grammar growth. This change introduces no new test suite or axiom policy.

### Required GALEC/Algorithm origins: standards impact

This increment follows `6c842847c2c1534d146f954afaa41f46d1598bb4`. It changes
required provenance in the existing DAE → GALEC → Solve Algorithm chain;
source admission, equation/initialization semantics, the unit sampling policy,
both EBNFs, and FMI/eFMI interface or archive layouts are unchanged.
The current normative clause map and its open findings therefore still apply.

The generated initialization value explicitly retains the MLS fallback and
unfixed-start selection parents. eFMI Startup/period and DoStep occurrences
retain separate generation rules; the sampling constant is not presented as a
written source constant. Exact origin-event preservation composes with the
existing GALEC-to-Solve lifecycle semantics. These are provenance guarantees,
not a proof of the still-open FMI lifecycle or eFMI coding-guideline clauses.

Sixteen new roots pass the unchanged axiom audit. The complete package gate
passed in `build/literal-call-worktree/build/galec-origins-package-gate-lean-only.log`
(3296 jobs), including both backend consumers and compiler contracts.
The main-workspace required full artifact gate passed in
`build/algorithm-provenance/full-gate.log`; its recorded source inventory
remained unchanged throughout the run. It retains the complete eFMU Startup
contract, independent extraction, native ME/CS and Production C checks, and
the existing actual-file mutation controls. This run produced:

- FMU SHA-256: `fcf9f72dd77e818f6f84ca1cf5201c9a80586f75fd07c9fcc4363db388e78477`.
- eFMU SHA-256: `5197818bc34e2ae7a401b869e9b1ebeb2dd0c8bd1aef3b8074f1a5f919f71e4b`.

No new test suite was added. **Stage decision: open** pending tensor/FMI
origin integration, actual emitted-byte maps and the earlier
whole-adapter/compliance obligations. No grammar expansion is authorized by
this provenance checkpoint.

### Required unit FMI IVP origins: standards impact

This increment follows `475f0a5` and strengthens preparation metadata for the
existing unit profile. Canonical source-table preservation is required through
Flat, DAE and Solve. The prepared FMI IVP requires every operation/operand
origin, including explicit rules for the empty input channel, state observation
and solver policy. The actual initial fill remains tied to the selected Solve
initial plan; a generated observation does not assert a source output qualifier.

The MLS 3.7 initialization/equation clause map, FMI 3.0.2 lifecycle/metadata
findings and eFMI Beta 1 Algorithm/Production Code review carry forward.
Neither EBNF, production source admission, numerical policy nor interface or
archive layout changes. These proofs do not close SR04, SR05, SR07 or SR08.

Nineteen added roots pass the unchanged audit, retaining every prior entry.
The final downstream package gate passed in
`build/literal-call-worktree/build/fmi-origins-trace-gate.log` (3305 jobs).
The main-workspace required full gate also passed in
`build/fmi-provenance/full-gate.log`, retaining the actual source-to-archive
Startup contract, native ME/CS and C boundaries, extraction/schema checks and
the existing mutation controls. Its source inventory remained unchanged. This
run produced:

- FMU SHA-256: `b8efa712c1758f1419f7ce83045983f6e3b231071498118db3cdb4152ada838c`.
- eFMU SHA-256: `cf46fbdc479e77328358fefa964a0990c0469d5165c5a54a46fc92424fb03eb8`.

No test suite was added. **Stage decision: open** pending development tensor
provenance, emitted-byte maps and the remaining
whole-adapter/compliance obligations. No grammar expansion follows this checkpoint.

### Shared C initialization origins: standards impact

This increment follows `59c538a`. It strengthens independent checking of the
actual GALEC block annotations and requires origins on the shared C initializer
consumed by FMI creation/reset. Its theorem combines exact source ancestry and
the annotation contract with all C-body behaviors under supplied writable
binary64 storage. It does not prove allocation or the complete public API.

The preceding MLS 3.7, FMI 3.0.2 and eFMI Beta 1 clause maps and findings carry
forward. Both EBNFs, source admission, numerical policy, rendered C expressions,
public interfaces and archive layout remain unchanged. No additional normative
conformance claim follows from the origin proofs.

Twenty-five added roots retain every previous audit entry and the unchanged
axiom policy. The downstream package gate passed in
`build/literal-call-worktree/build/c-initial-provenance-package-gate.log`
(3316 jobs). The required main-workspace artifact gate also passed in
`build/c-initial-provenance/full-gate.log`, including both target archives and
the existing boundary/mutation checks. All 510 inventoried inputs remained
unchanged. This run produced:

- FMU SHA-256: `0cc3e17ec9052f3738a61ab108e3699b3dd7d241370bb731fc76cee28edb96ab`.
- eFMU SHA-256: `5c4e3af3b5768c2f06948d979b845efdcb31f3d5ae7544b58b13bb55f720820c`.

No new test suite is added.
**Stage decision: open.** Remaining byte maps, full adapter/artifact composition
and unresolved standards findings continue to block grammar expansion.

### Shared initializer printer map: standards impact

This increment follows `22c44f7`. It adds exact maps for the shared C
initialization fragment, with unchanged production printers, grammar admission,
numerical policy, public interfaces and archive layout. The existing MLS 3.7,
FMI 3.0.2 and eFMI Beta 1 clause maps and unresolved findings carry forward.

The formal contract combines the actual statement printer's UTF-8 bytes,
complete range collection, exact byte extraction, source ancestry and the
existing all-behavior initialization theorem. It assumes supplied writable
binary64 storage and the explicit `double` binding. Whole-function/file and
archive-member map correspondence remain open; no new normative conformance
claim follows from this fragment result.

All 186 prior C audit roots are retained, with 25 additions under the same
axiom policy. The downstream package gate passed in
`build/literal-call-worktree/build/c-mapped-initialization-package-gate.log`
(3319 jobs). The required main-workspace artifact gate also passed in
`build/c-mapped-initialization/full-gate.log`, including both target archives and
the existing boundary/mutation checks. All 513 inventoried inputs remained
unchanged. This run produced:

- FMU SHA-256: `0ef7c4543ee7481fbcafabebdc1cb8737e80cc5ea173f3b12f3da5874d792dc2`.
- eFMU SHA-256: `caa2b6d1f7359897d77ce5a4f75fc2fa1547011f7c4a7de8c04ca034dc388fc1`.

No test suite was added. **Stage decision: open.** The remaining map, adapter/artifact
and standards obligations continue to block grammar expansion.

### Shared statement/function maps: standards impact

This increment follows `f13710e`. It adds required annotations and mapped
printers for existing C syntax and migrates the shared initializer to that
statement path. Exact output bytes and all prior initializer execution/map
contracts are preserved. No source admission, numerical policy, public
interface or archive layout changes. The MLS 3.7, FMI 3.0.2 and eFMI Beta 1
clause maps and unresolved findings carry forward.

The generic map contracts preserve supplied origin predicates and exact UTF-8
segments. They do not prove that every production function has received the
correct source/rule attachments, nor certify arbitrary C syntax or establish
whole-file/archive maps. No new normative conformance claim follows.

All 211 earlier C audit roots are retained, with 24 additions under the same
axiom policy. The downstream package gate passed in
`build/literal-call-worktree/build/c-statement-function-map-package-gate.log`
(3324 jobs). The required main-workspace artifact gate passed in
`build/c-statement-function-map/full-gate.log`, with all 517 inventoried inputs
unchanged and both actual target archives checked. No new test
suite is added. **Stage decision: open** pending the remaining producer/map,
adapter/artifact and standards obligations; grammar expansion remains blocked.

This run produced the retained artifacts:

- FMU SHA-256: `baf7f47847d2219d38b6a5fdd48ca0f1a073c27037537a560cf89527413db2aa`.
- eFMU SHA-256: `619669cd9e8009a04174f26fad2b057fcb6b33b0012c371e2003cce59018106f`.

### eFMI Startup maps: standards impact

This increment follows `798aec4`. Production and archive export now use the
Startup map renderer; a theorem proves that the complete C bytes remain
unchanged. Its origins come from the prepared Solve trace, with separate shared
C instruction and eFMI interface rules. The production contract additionally
requires exact complete-file map ranges, independent annotation requirements,
distinct state/period source ancestry and every Startup execution behavior.
Existing source, numerical, metadata, interface and archive-layout contracts
are retained. No source admission or standards-profile change occurs; the
MLS 3.7, FMI 3.0.2 and eFMI Beta 1 clause maps/findings carry forward.

All 105 earlier eFMI production audit roots remain, with 22 additions under the
unchanged axiom policy. All downstream package checks passed in
`build/literal-call-worktree/build/efmi-startup-map-package-gate.log` (3337 jobs).
The required main-workspace artifact gate passed in
`build/efmi-startup-map/full-gate.log`, with all 522 inventoried inputs unchanged.
It checked both actual archives and the existing native, extraction, schema,
checksum, mutation and publication controls. Retained products:

- FMU: `66da9eb46b57b878f89c0b6c89627d50221614a3fc86a66ab2ee7aab3647c2aa`.
- eFMU: `d2fb726a2387bd1608fa743674f49b54899c4232957c871f90dca975918a853a`.

The computed map applies to Startup and the certificate's supplied input. Header/later-method
maps, archive map serialization and original-to-staged input identity remain
open. No additional test suite was created. **Stage decision: open**; existing
adapter/artifact and compliance findings continue to block grammar expansion.

### FMI reset and adapter-byte binding: standards impact

The candidate on top of `a40022e` leaves both EBNFs, production admission,
emitted C, metadata and archive contents unchanged. The header reader's
accumulator implementation preserves its earlier behavior by theorem. MLS 3.7
and eFMI Beta 1 clause mappings above remain applicable to this unit profile;
there is no new source or GALEC case.

| Applicable obligation | Added proof correspondence | Remaining obligation |
| --- | --- | --- |
| MLS §§4.9 and 8.6: stored Real values and selected initialization. | The complete reset call's returned heap supplies the finite value used by `ResetSourceResult`, with the same compiled Solve default and unique initialized source trajectory. | Reset does not add an initial source equation. Host-set/initialization composition and SR08 remain open. |
| FMI 3.0.2 §2.3.1: reset restores defaults and Instantiated; initialization precedes a new run. [Normative reset clause](https://fmi-standard.org/docs/3.0.2/) | `Reset.correct` and `Reset.FunctionContract` cover termination, eight writes, default state, clock/stop fields and all other memory cells for both interface kinds and declared modes. | Allocation and equivalence to a freshly instantiated object, logging/callback policy and complete cross-call lifecycle composition remain open. |
| FMI §2.2.4: error recovery and instance isolation. | Reset also covers Terminated; `other_instance` preserves every cell in other blocks. | General error/callback execution and native object layout remain outside this result. |
| FMI C source artifact binding. | `SourceBuildContract.adapter` requires exact complete adapter bytes, unique printed definitions, the reset signature and its independently specified function/call contract. | Whole translation-unit/preprocessor meaning, official-header/ABI correspondence, all other public bodies and complete archive composition remain open. |
| eFMI Algorithm/Production Code. | Existing DAE→GALEC→Solve, Startup and production/archive contracts are retained. | This FMI-only increment closes no eFMI finding. |

The 27 new roots and existing package audits pass under the unchanged axiom
policy. The focused printer certificate and added reset-body mutation pass.
The complete fixed actual-file check passes in `build/fmi-reset/actual-file.log`;
the required main-workspace gate also passed in `build/fmi-reset/full-gate.log`,
with all 529 inventoried inputs unchanged and both target archives checked.
The integrated checker reuses the
existing character-join theorem and kernel-checked segment composition to
reduce proof-checking cost without changing its proposition.
**Stage decision: open**; SR04, SR05, SR07,
SR08 and the remaining provenance/adapter obligations continue to block growth.
See [the precise contract](fmi3/contracts.md#reset-and-complete-adapter-bytes).

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

**Rejected public-call follow-up:** [ErrorCalls](../packages/backend-fmi3/RumocaFMI3/ErrorCalls.lean)
now supplies ordinary string-pointer parameter binding and composes the
nominal-query rejection through the failure helper's return with logging
disabled. Its all-behavior theorem includes the exact mode change and memory
frame. The [pointer/call checkpoint](#c-literal-pointer-and-rejected-call-increment-standards-impact)
records the full local gate and actual artifacts. Enabled callbacks, literal
global setup and complete printed adapter binding still prevent SR04 closure.

### SR05 — resolved for the unit initialization policy

At `d519438`, [Runtime.body](../packages/backend-fmi3/RumocaFMI3/Runtime.lean) rejected enabled
`stopTime <= startTime` and `tolerance <= 0` for both interfaces. On the actual
binary, zero-duration and zero-tolerance initialization each return Error;
ordinary initialization returned OK. The theorem at that revision correctly
proved the authored strict policy.

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

The [initialization correction](#complete-initialization-calls-standards-impact)
implements and proves the inclusive-stop/unused-tolerance policy together with
complete failure, logging and source-IVP contracts. Its actual-file requirement
is integrated and the required full gate passed with 706 unchanged inputs.
This resolves the scoped admission-policy finding. Cross-standard
initialization correspondence (SR08), instance lifetime, other public calls,
native ABI and MISRA findings remain open; no whole-stage closure follows.

### SR06 — resolved packaging question: documented checker limitation

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

**Review disposition (2026-09-10):** the standalone layout is permitted by
[Beta 1 Chapter 2](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
Its second package format places the eFMU contents, including `__content.xml`,
at ZIP root with the `.efmu` extension. Its embedded FMU format instead uses
`extra/org.efmi-standard`. The pinned checker's
[entry checks](https://github.com/modelica/efmi-compliancechecker/blob/edf33452ed0628bde1d8102c77b1030259ad5f57/sources/eFMIComplianceChecker/eFMIComplianceChecker.py#L123-L170)
require `.fmu` and `eFMU/`; they do not implement the selected standalone format.
The specification archive SHA-256 and checker commit above were rechecked.

SR06 is resolved as an explicit tool limitation, with no production-layout or
verification-contract change. The loop/call checkpoint's complete local gate
checks the actual standalone archive and independently extracts its members,
schemas and checksum graph. The wrapped checker's deeper pass remains evidence
for the earlier, identified diagnostic copy only. **There is no official-checker
pass for the current standalone artifact.**

Reopen this disposition if the normative version, checker revision or selected
package format changes. It does not waive failures in member contents, GALEC,
Production C or manifests, nor close SR07, SR08 or the remaining E05/E06 proof
and release obligations.

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
4. Retain SR06's documented disposition and close the SR07 release review
   obligations before claiming standards compliance or assurance comparable
   to an established verified compiler.

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


## Static runtime and public factory composition checkpoint — 2026-09-13

This incremental review records progress within the frozen stage. It is not a
completed recurring stage checklist, a grammar expansion, or a MISRA declaration.

- **FMI 3.0.2 §§2.2.1, 2.3.1:** the emitter uses 32 permanent shared ME/CS
  objects and bounded atomic reservation/release. The derived public-call
  theorems cover supported creation, sequential exhaustion, unsupported CS
  requests, missing/invalid identities, exact diagnostics, optional logging,
  immediate release/reuse and null release. Logging disabled implies no logger
  invocation; enabled logging retains all represented callback outcomes and
  effects. The initial value is tied to the compiled Solve plan. Full host
  histories, other-instance callback frames, native concurrency and subsequent
  initialization/operation composition remain open. Normative reference:
  [FMI 3.0.2](https://fmi-standard.org/docs/3.0.2/).
- **MLS 3.7:** source grammar, parser, lowering and numerical Solve semantics
  are unchanged. The unit derivative does not itself specify an initial value;
  the checked fallback plan selects zero and retains its existing notices.
  The creation theorem proves the stored binary64 value agrees with this plan
  and selects the unique completed source trajectory.
- **eFMI 1.0.0 Beta 1 Algorithm/Production Code:** the full static-runtime gate
  passed actual eFMU archive/source/native/mutation controls. Algorithm Code and
  Production C members are byte-identical to the published checkpoint. Their
  existing normative findings and correlated-product obligations remain open.
- **MISRA C:2025/C11:** generated factory/release code no longer calls dynamic
  allocation. Static declarations and selected atomic calls have authored
  semantics and printer contracts. The existing native checks passed pool
  exhaustion, isolation/reuse and allocator/out-of-line-atomic import checks.
  These do not prove a transitive no-heap policy or native atomic semantics.
  Essential types, remaining pointer guards, floating comparisons, native
  size/alignment/profile and the guideline matrix still block conformance.
- **Architecture:** Rust SPEC_0007 at
  `b102b3f710eb232880728d4e474292cfb07d5ce0` was rechecked. Numerical
  initialization stays in Solve, with DAE → GALEC → Solve for eFMI and
  DAE → Solve for FMI. These changes add no name resolution, shape inference,
  equation lowering or solver selection to a backend.

Evidence: `build/c-factory/static-runtime-full-gate-v1.log/.exit` passed for
793 unchanged inputs and both actual target archives. Thirteen later roots
passed two focused package audits, the last with 798 unchanged draft inputs and
all 760 published inputs unchanged. Earlier semantic/emitter/mandatory-contract
definitions and every audit root were retained. The current seven-root increment
adds three compiler proof modules and audit entries, with no new test suite.
These later package checks are not a new full artifact gate. The detailed
record is `build/c-factory/static-runtime-review-v1.md`.

**Decision:** stage remains open; do not expand the grammar or claim whole
FMI/eFMI, MISRA, native machine-code or aircraft assurance completion.

### Static creation through initialization — 2026-09-13

Seventeen additional audit roots connect creation, EnterInitialization and
ExitInitialization in one actual object-aware program. The generic C body
bisimulation proves local binding changes preserve returned values/heaps,
failure and divergence. The FMI instance proves syntax lookup and type
agreement, complete successful/null calls, and the storage premises derived
from creation. The compiler consequence retains the exact intermediate heaps,
clock, lifecycle mode, reservation flags, slot metadata and the actual finite
value's agreement with the Solve plan and completed source solution.

[FMI 3.0.2 §§2.3.2–2.3.3](https://fmi-standard.org/docs/3.0.2/) were rechecked:
initialization uses the supplied start time; exit activates ME event equations
and, with CS event mode unused in this profile, CS stepping. The theorem uses
the existing admissible finite-time profile and makes no new tolerance,
variable-step or event capability claim. Host setters and invalid subsequent
calls still need composition in this same interface. MLS/GALEC grammars,
numerical semantics and eFMI members are unchanged. Rust SPEC_0007 at
`c89fde703f82afc323d9f38bdf1e8f316452d723` retains the same DAE/GALEC/Solve
ownership boundaries; the backend reuses prepared Solve initialization.

The C/FMI/compiler package audit passed for 801 unchanged inputs in
`build/c-factory/static-initialization-packages-v1.log`; the strengthened
compiler consequence passed `static-initialization-packages-v2.log`. No prior
emitter, semantics, mandatory contract or audit root was removed or weakened.
No test suite was added. The required main-workspace integration gate then
passed with all 801 source inputs unchanged in
`build/c-factory/static-integration-full-gate-v1.log`. Its FMU/eFMU archives
and member comparisons are retained under `build/c-factory/`; only the FMI
adapter C differs from the preceding allocating artifact. Numerical C,
FMI metadata, GALEC and eFMI Production C are unchanged. Subsequent
current-status documentation cleanup changes no code or audit input.
Concurrent histories, callback frames, remaining API behavior, native ABI,
no-heap policy and MISRA obligations keep this stage open.

### Static initialization error coverage — 2026-09-13

The derived source/adapter consequence now covers successful/null calls and
initialization rejection with disabled, missing or enabled supplied logging.
The preceding initialization error contract omitted the missing-logger/enabled
flag case; the emitted guard already suppressed it. The new contracts prove
that behavior and the exhaustive nullable-pointer/Boolean case split. The
actual definitions and immutable diagnostics come from the same prepared
artifact on heaps that can include writes by earlier calls.

[FMI 3.0.2 §§2.2.1 and 2.3.1](https://fmi-standard.org/docs/3.0.2/) permit
null callbacks to identify unavailable functionality and restrict its use;
SetDebugLogging with a missing logger, for example, has undefined standard
behavior. These proofs describe the existing defensive error path; they do
not authorize arbitrary use of missing callback support. Disabled logging
causes no callback. Supplied loggers receive the Error status/category/message,
with all modeled effects retained. Native callback execution, private-storage
frames and non-reentry correspondence remain open.

The 22 new roots passed the focused FMI/compiler package audits in
`build/c-factory/static-error-package-gate-v2.log`, with 804 unchanged draft
inputs and the 801 main gate inputs unchanged. The latter full artifact gate
and its retained FMU/eFMU cover the same emitters and mandatory contracts.
No previous definition or audit root was weakened and no test suite was added.
MLS 3.7 and eFMI 1.0.0 Beta 1 language/output profiles are unchanged. Rust
SPEC_0007 at `5d0f62d147caa94e04befb9532f437b0b16cb9de` retains the reviewed
DAE/GALEC/Solve ownership. This is an incremental review within the frozen
stage; whole host histories, remaining APIs, native ABI, no-heap/MISRA and
the other recurring checklist findings remain open.
