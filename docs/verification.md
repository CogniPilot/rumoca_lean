# Exact verification contract

**Latest storage checkpoint (2026-09-13):** this working source emits 32
permanent, shared ME/CS instance slots with bounded atomic reservation and
release. Its mandatory adapter contract now includes declaration syntax,
record interpretation, capacity bounds, initial creation/release execution
and consistent foreign bindings. The full artifact gate passed for the
793-input static-runtime snapshot in `build/c-factory/static-runtime-full-gate-v1.log`.
The retained FMU/eFMU and source/member comparisons are under
`build/c-factory/static-runtime-artifacts-v1/` and the adjacent review files.

Thirteen subsequent derived theorems connect the actual source token, literal
pool and function table to creation, exhaustion, input rejection, optional
logging, immediate release/reuse and the stored Solve/source initial value.
Their package audits passed in `static-creation-consequences-packages-v1.log`
and `static-public-consequences-packages-v1.log` under `build/c-factory/`.
The latter check covered 798 unchanged inputs; the full artifact gate was not
rerun for these proof-only additions. Every earlier emitter, semantic
definition and mandatory contract field was retained. The earlier published
`2628f35` checkpoint used the allocating emitter.

Seventeen further audit roots now connect creation to both complete public
initialization calls in the same execution interface. A shared body
bisimulation proves that changing unused global bindings preserves all body
behaviors; it does not assume agreement for unrelated factory definitions.
The actual adapter supplies function membership and definitions. Creation
supplies writable storage, initial mode and the finite Solve default; the
composed theorem retains the exact intermediate heaps, initialized clock,
ME Event/CS Step mode, slot metadata and ownership, and the unique completed
source solution. Successful and null initialization calls are covered;
invalid subsequent calls and arbitrary host histories remain open.
`static-initialization-packages-v1.log` passed C/FMI/compiler checks for 801
unchanged inputs, and `static-initialization-packages-v2.log` passed the
strengthened compiler consequence. These logs are under `build/c-factory/`.
No earlier emitter, semantic definition, mandatory contract or audit root
changed. The full main-workspace gate then passed in
`build/c-factory/static-integration-full-gate-v1.log`, with all 801
integration inputs unchanged. Both actual FMU interfaces and the eFMU
passed their existing artifact/native/rejection checks. The adjacent
`static-integration-artifacts-v1/` retains the checked archives; member
comparisons confirm unchanged numerical C, FMI metadata, GALEC and eFMI
Production C. The status-document reconciliation after this gate changes
only these three documentation files; code and audit inputs are identical.

Twenty-two subsequent derived audit roots connect complete initialization
error paths to the same static object environment and actual function table.
They preserve all represented callback outcomes, immutable diagnostic bytes,
and the path with no returning callback outcome. A review found an omitted
case in the earlier error contract: logging enabled with no logger. The new
suppressed contracts cover a missing logger or disabled logging; a theorem
proves that these cases and an enabled supplied logger exhaust the represented
domain. The generated C already handled this case, so no emission changed.
`build/c-factory/static-error-package-gate-v2.log` passed the FMI/compiler
package audits with all 804 draft inputs and all 801 main gate inputs unchanged.
The full artifact result belongs to the preceding 801-input snapshot; these
new derived consequences have separate package evidence. Existing emitters,
semantics, mandatory artifact contracts and audit roots were retained. No new
test suite was added. See `build/c-factory/static-error-review-v1.md`.

Reset now uses this same object interface too. Fifteen further derived audit
roots cover complete successful/null calls and reset followed by both public
initialization calls. Every intermediate heap is explicit; reset supplies the
new initialization storage, restores the Solve default and establishes the
corresponding source IVP. Frame proofs preserve lease flags, slot metadata and
arbitrary nested fields of other instances in the same array. The FMI/compiler
package audits passed in `build/c-factory/static-reset-package-gate-v1.log`
with all 806 inputs unchanged. This adds proofs only: earlier semantics,
emitters, mandatory artifact contracts and audit roots are retained. The
previous full artifact gate still supplies the unchanged C/archive evidence;
it was not rerun for these derived consequences. No new test suite was added.

This does not close K02–K05. Remaining public calls must be composed in the same
object-aware execution interface; actual concurrent histories, callback
frames, a transitive no-heap/call-graph policy, native ABI/profile and MISRA
correspondence remain open. The production grammar is unchanged. Earlier
paragraphs below record historical checkpoints, including the former
allocating implementation; they do not supersede this storage status.

**Current claim boundary:** the numerical source-to-C core is formally
checked. The whole FMI/eFMI compiler is not yet fully verified, even for the
unit grammar subset, because the adapter/artifact/compliance obligations
below remain open. Completing this stage requires one composed guarantee for
the actual compiler and production artifacts, with every pass and admitted
interface behavior covered. Individual theorem or CI checkpoints are partial
progress and do not authorize grammar or product-scope expansion.

Before every spiral-stage grammar expansion, the admitted subset must also
complete a recorded review against MLS 3.7, FMI 3 ME/CS, and eFMI Algorithm and
Production Code, using the [recurring stage checklist](../dev/standards-review.md#required-review-at-every-spiral-stage).
That review maps normative clauses to the authored semantics,
pass/target proofs, actual-artifact contracts and explicit external assumptions.
Open compliance findings block expansion. Kernel checking proves the authored
propositions; review against the prose standards is a separate obligation.

The production end-to-end theorem covers one Modelica `Real` state and `der(state)=1`.
The source equation is over mathematical reals. Generated C uses finite
IEEE754 binary64 values and nearest-even addition. The numerical theorem takes
a supplied finite `x(0)`; samples remain at integer times. There is no initialization syntax, variable
time step, event handling or general solver. All compiler code, EBNF tooling,
semantics and proofs are Lean. No Rocq dependency or cross-prover assumption
is used.

The default IVP now has an explicit checked initialization plan. The source
relation remains underdetermined: `der(x)=1` does not imply `x(0)=0`. Preparation
selects the Real fallback zero and records both fallback and unfixed-start
selection notices. Scalar Flat/DAE/Solve models require exact occurrence origins
and preserve those settings; CLI and LSP notices identify the declaration.
The shared C initializer proves its write and memory frame, and FMI emits it
on instance activation and reset. Whole FMI storage/lifecycle/host-set and
artifact composition remain open.

`EFMIInitializationProofs` derives the completed source trajectory from the
finite state actually loaded after Production C Startup. For every admitted
entry heap, `ArchiveStartupContract` binds the exact archive member and its
independently denoted C tree, proves termination and characterizes all Startup
behaviors. The actual archive checker now requires this consequence together
with its prior contract. Entry storage, public ABI and later machine compilation
remain explicit boundaries. The final required gate passed in
`build/initialization-provenance/full-gate.log`, with its source inventory
unchanged throughout the run. See
[initialization.md](../dev/initialization.md) for remaining SR08 obligations.

GALEC and Solve Algorithm models now also require complete origin traces.
Independent rule/parent requirements identify initialization, sampling policy,
methods, state accesses and assignments. The composed lowering theorem
preserves both lifecycle values and every operation/operand origin event,
without enumerating tensor elements. Sixteen added roots retain the existing
axiom policy; the required full gate passed in
`build/algorithm-provenance/full-gate.log`, including both target archives.
At that checkpoint tensor/FMI operation origins and actual emitted-byte source
maps remained open; this does not close the whole-adapter/compliance contract.

The subsequent unit FMI preparation now requires complete indexed origins too.
`FMI3Model.preparation_preserves` connects the actual tensor IVP's initial value,
RHS and observation to its stored Solve model, and proves exact source lookup,
generated-role ancestry and an independent contract for the attached operation
annotations. Nineteen new roots and the downstream package gate pass in
`build/literal-call-worktree/build/fmi-origins-trace-gate.log`. The required full
main-workspace gate also passed in `build/fmi-provenance/full-gate.log`, including
both actual target archives with the input inventory unchanged throughout.
Development tensor/AD provenance, actual C/GALEC/XML byte maps and complete
adapter/artifact composition remain open. No source grammar case is added.

The next increment strengthens the actual GALEC annotation contract and adds
required origins to shared C initialization emission. `GALEC.Model.TraceCorrect`
inspects the annotations on the actual block; Solve Algorithm lowering now
preserves this contract alongside its existing values and origin events.
`CInitialization.Emission.preserves` combines the actual initializer's annotation
contract, declaration ancestry and all terminating C-body behaviors. It assumes
the supplied target denotes writable binary64 storage and the interface binds
`double` accordingly. FMI creation/reset use this checked emission. Allocation,
the enclosing public functions and emitted-byte source maps still require
separate composition. Its 25 added audit roots and downstream package checks
passed in `build/literal-call-worktree/build/c-initial-provenance-package-gate.log`;
the required main-workspace artifact gate also passed in
`build/c-initial-provenance/full-gate.log`, including both actual target archives
and the existing boundary/mutation checks. All 510 inventoried inputs remained
unchanged throughout the run.

The following shared-initializer map increment proves exact correspondence
between its required origins and the existing statement printer's UTF-8 bytes.
`CInitialization.Emission.printed_preserves` combines the execution contract
with annotation correctness, ancestry of every collected map entry, complete
range membership and exact byte extraction. Generic expression mapping preserves
the existing printer and every annotated origin; a single array collector uses
cached document lengths. These 25 new audit roots and all downstream package
checks passed in
`build/literal-call-worktree/build/c-mapped-initialization-package-gate.log`.
Its required main-workspace artifact gate also passed in
`build/c-mapped-initialization/full-gate.log`, with all 513 inventoried inputs
unchanged and both actual target archives checked. This is a fragment map:
whole-function/file maps, original-to-staged input identities and archive-member
map binding remain open, along with the adapter obligations above.

The next increment adds complete annotations and mapped printing for the
existing C statement, parameter, signature and function syntax. It proves exact
printer-byte equality, range extraction and preservation/reflection of predicates
on supplied origin references. The initializer now derives a complete statement
trace and uses this shared mapper; its earlier map and execution contracts are
retained. Twenty-four additional audit roots and downstream package checks pass
in `build/literal-call-worktree/build/c-statement-function-map-package-gate.log`.
The required main-workspace artifact gate passed in
`build/c-statement-function-map/full-gate.log`, with all 517 inventoried inputs
unchanged and both actual target archives checked. These generic maps do not
establish correct source/rule attachment in every production function, arbitrary
C-tree validity, whole-file/archive map binding or full adapter execution.

The next eFMI increment connects those maps to the actual Production C Startup
emitter. Required annotations come from prepared Solve operations and operands;
independent predicates inspect every Startup annotation and its generating
rule/parents. The state default traces to the declaration, while the generated
sampling period traces to the model policy. `ProductionContract.startup_map`
requires the exact file bytes, complete Startup map ranges, source ancestry and
all Startup behaviors in one witness. Both production and archive generation
consume the mapped renderer; `StartupMap.render_unchanged` preserves the earlier
C text and execution contracts. All package checks and 22 new audit roots pass
in `build/literal-call-worktree/build/efmi-startup-map-package-gate.log`.
The required main-workspace artifact gate passed in
`build/efmi-startup-map/full-gate.log`, with all 522 inventoried inputs unchanged
and both actual target archives checked. This certifies a computed
Startup map against the supplied input and complete C member, not a serialized
archive map. Header/other-method maps, original-to-staged input identity and
the remaining adapter/standards obligations are still open.

The current FMI reset increment has package-checked complete-call, frame,
independent function-syntax and source-initialization proofs. Its strengthened
actual-file contract binds the complete adapter renderer to the file and the
same definition table used by the reset theorem. The fixed actual-file check
passes in `build/fmi-reset/actual-file.log` under the unchanged axiom policy;
the required root gate also passed in `build/fmi-reset/full-gate.log`, including
both actual target archives with all 529 inventoried inputs unchanged. This
does not close other adapter bodies, allocation,
whole-C/preprocessing or ABI obligations; see
[the reset contract](../dev/fmi3/contracts.md#reset-and-complete-adapter-bytes).

The shared CTree printer now proves character stability under trigraph
replacement and line splicing for every expression, statement and function.
Its FMI instantiation covers the complete adapter renderer. The strengthened
`FMI3.AdapterContract` requires this guarantee for the actual file, deriving
model-name safety from source lexing and checking signature spellings in the
kernel. All 35 new roots and affected package audits pass in
`build/source-cutover/build/c-printer/composed-package-audit.log`; the fixed
checker also passes on the retained FMU files in its `actual-fmi.log`.
The required main artifact gate passed in `build/c-printer/full-gate.log`, with
all 596 inventoried inputs unchanged and both actual archives checked. Exact
archives and hashes are retained in `build/c-printer/artifacts/`.
This does not establish C tokenization, macro/header interpretation, remaining
public-call behavior or whole FMI/eFMI compliance. See
[the printer roadmap](../dev/c-printer.md).

The follow-on shared printer now derives the independent token/precedence
grammar of every admissible CTree expression, block item and complete function.
Names, typedef spellings and postfix restrictions are explicit premises;
indentation, nested statements and call/parameter lists are universally
quantified. The actual reset contract additionally requires this generic
text/tree judgment, and `adapter_reset_syntax` binds its fragment to the complete
adapter file. Existing execution, memory and character-rewrite contracts remain
required. This is not a full C tokenization theorem: cross-category maximality,
adjacent-string concatenation, macros/headers and other public calls remain
open. All 85 added roots and affected packages pass
`build/c-token/final-package-audit.log`. The required actual-artifact gate passed
in `build/c-token/full-gate.log`, with all 613 inputs unchanged and both actual
archives checked. Exact artifacts and hashes are retained in
`build/c-token/artifacts/`. No grammar or emitted
C bytes change. See [the exact scope](../dev/c-printer.md).

The next lexical increment now proves cross-category maximality for the
compositional token judgments against an independent normal-context candidate
envelope. It checks identifier/number competition, literal encoding prefixes,
all punctuators and comment openers against the actual continuation. The
independent function grammar separates ordinary literals, so no phase-six
concatenation changes its tokens. `FunctionDenotes.tokenization` composes these
results using one token witness, and the actual reset contract now requires
this consequence alongside its prior syntax, call and memory contracts.
`adapter_reset_tokenization` locates that certified fragment in the complete
adapter file. All 67 added audit roots and affected packages pass
`build/c-lexical/composed-audit.log`. The required full gate passed in
`build/c-lexical/full-gate.log`, with all 621 inputs unchanged and both actual
archives checked. Exact archives and hashes are retained in
`build/c-lexical/artifacts/`.
No C bytes or grammar cases change. This is an ordinary-code contract;
header-name/directive contexts, macro expansion, actual typedef meanings,
scope/type constraints and remaining public-call behavior stay open.

The following increment requires the independent shared grammar for the
complete actual FMI function section. `function_sequence_tokenization`
composes arbitrary lists with their real lexical continuations, and
`RuntimePrinter` instantiates it for all runtime bodies and helpers.
`AdapterContract` retains every prior field and additionally binds that section
to the exact adapter bytes and prepared definition table. The fixed checker
kernel-checks type/name proofs for its collected signatures; it does not assume
the header collector is correct. `adapter_reset_source` now retains this
grammar witness alongside the reset execution/source consequence for the same
table. Nine new roots and the affected packages pass
`build/fmi-functions/package-audit-v2.log`. The fixed actual-file checker passes
in `build/fmi-functions/actual-fmi.log`. The required full gate passed in
`build/fmi-functions/full-gate.log`, with all 625 inventoried inputs unchanged
and both actual archives checked. Exact archives and hashes are retained in
`build/fmi-functions/artifacts/`. Typedef meanings, headers/macros, declarations,
scope/type constraints and other public-call execution remain open. No runtime
or source grammar changes. At that checkpoint, 57 of the 75 collected API signatures
contained an adjusted parameter type absent from its execution dictionary;
the new grammar contract does not supply those missing conversions. See the
[concrete F03 review](../dev/fmi3/contracts.md#reset-and-complete-adapter-bytes).

The current call-entry increment addresses those missing parameter bindings.
`CallSignature.call_entry` derives a fresh coherent scope from per-parameter
conversion, while `arguments_exist` establishes a nonempty argument domain.
`CUnsigned` proves modular integer conversion, uniqueness and BitVec agreement;
FMI selects 32 bits for value references. `AdapterContract` retains its previous
fields and requires known parameter/return types and unique parameter names for
every actual helper/API function. `adapter_call_entry` binds their entry theorem
to the same actual bytes and grammar witness. This does not establish body
termination/effects, pointee storage, callback execution or native header/ABI
correspondence. All 26 new roots and affected packages pass
`build/fmi-types/package-audit-v2.log`. The strengthened actual-file checker
passes in `build/fmi-types/actual-fmi.log`. The required full gate passed in
`build/fmi-types/full-gate.log`, with all 629 inventoried inputs unchanged and
both actual archives checked. Exact archives and hashes are retained in
`build/fmi-types/artifacts/`; their C and GALEC members match `fe4ebef`. No source
grammar or runtime emitter changes.

The next count-query increment requires complete calls for both existing ME
count getters in `AdapterContract`, together with successful literal-pool
construction. The actual `SourceBuildContract` now binds the complete metadata
tree through `XML.Document`, in addition to its prior identifier contract.
`counts_source` joins actual C grammar, complete successful-call behavior,
returned counts, Solve state volume and an independent scalar-reference count
relation for the actual XML. Null instances are covered too. Invalid lifecycle
and missing-output calls have complete Error/Terminated results with logging
disabled; `counts_failure_source` constructs their collected literal addresses
and immutable objects and proves their heap frame. Enabled callbacks, native
allocation/header/ABI meanings, other public calls and full FMI conformance
remain open. No source grammar or emitted C/GALEC changes. All 28 added roots
and affected package checks pass
`build/fmi-counts/package-audit-v2.log`. The strengthened actual-file checker
passes in `build/fmi-counts/actual-fmi-v2.log`. The required full gate passed in
`build/fmi-counts/full-gate.log`, with all 634
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-counts/artifacts/`; their C and
GALEC members match `d147774` (`code-member-comparison.log`).

The version-query increment now requires the actual `fmi3GetVersion` function's
grammar, constructed static storage and complete behavior in `AdapterContract`.
`version_source` connects its immutable, zero-terminated `3.0` result and
unchanged heap to the version fields of both actual XML documents. No instance
or lifecycle premise is needed. This uses the authored C interface; native
header/ABI interpretation and the remaining public functions stay open.
All 11 new audit roots and affected packages pass
`build/fmi-version/package-audit.log`. The required full gate passed in
`build/fmi-version/full-gate.log`, with all 637
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-version/artifacts/`; their C and
GALEC members match `f9702f9` (`code-member-comparison.log`).

The callback increment uses a shared `Typed.nextWith` scheduler and labeled
execution with finite/infinite histories. Existing internal-call, literal and
read-only proofs remain required. The actual adapter contract now also requires
`Logging.FunctionContract`: `logging_source` binds the emitted failure helper,
its prepared function table, constructed `logStatus` bytes and actual XML
category. Enabled calls emit the importer symbol and converted environment,
Error status, category and message pointers, then return Error with the host's
permitted writable effects. Immutable category/message storage survives.

This is conditional on the explicit symbolic callback binding, the pinned
prototype and an invocation-local returning host effect. It does not establish
arbitrary callback termination, native function-pointer ABI, allocation,
reentrancy or complete public-call/FMI conformance. At this checkpoint,
named-literal lowering retained its internal-machine contract; the eventful
extension was still separate from the emitted-helper proof. No source grammar,
renderer or boundary test suite is added. All 58 new audit roots and affected
packages pass `build/c-events/package-audit-v1.log`. The required full gate
passed in `build/c-events/full-gate.log`, with all 646 inventoried inputs
unchanged and both actual target archives checked. Exact archives and hashes
are retained in `build/c-events/artifacts/`; their C, header and GALEC members
match `c522107` (`code-member-comparison.log`).

The subsequent eventful literal pass preserves and reflects every authored C
behavior, including callback arguments/effects, faults and finite or infinite
event histories during divergence. Both interface extension and syntax lowering
instantiate labeled bisimulation; ordinary and eventful calls share scheduler
proofs. `AdapterContract` now requires `LiteralPreparation.EventContract` for
its actual function table and separately requires successful pool preparation.
`literal_events_source` and the strengthened `logging_source` retain the actual
file/table/pool witnesses. Foreign relations are unchanged; the pass adds no
callback determinacy or successful-return premise. This does not model execution
inside a nonreturning foreign call or establish native header/ABI correspondence.
All 37 new audit roots and affected package checks pass in
`build/c-events/literal-package-audit-v1.log`. The required full artifact gate
passed in `build/c-literal-events/full-gate.log`, with all 651 inputs unchanged
throughout the run. Both target archives are retained in its `artifacts/`
directory; their C, header and GALEC members match `d529b5d`
(`code-member-comparison.log`). See
[the pass contract](../dev/fmi3/contracts.md#eventful-literal-lowering).

The all-outcome helper increment strengthens the mandatory logging contract
with both `AllPreparedContract` and `SilentPreparedContract`. Enabled logging
characterizes every represented returning host effect without a supplied
successful outcome or determinacy premise; absence is explicitly stuck in the
atomic external machine. Disabled logging proves no callback events and exactly
the mode write. The same actual-file/table/pool/XML witnesses and eventful
literal-lowering contract remain required. Shared silent-prefix and external
choice theorems support the actual helper's dispatch and return continuation;
earlier determined guarantees are retained as consequences.

Compiler composition builds in `build/c-logging-choices/promotion-v2.log`.
All 21 new roots and affected package checks pass in
`build/c-logging-choices/package-audit.log`; every earlier audit root is retained.
The required full artifact gate passed in
`build/c-logging-choices/full-gate.log`, with all 654 inputs unchanged and both
actual archives checked. Retained archives and hashes are in
`build/c-logging-choices/artifacts/`; their C, header and GALEC members match
`7004a3e` (`artifact-retention.log`). This does not prove execution
inside host calls, native ABI, allocation, host ownership or all public entries.
FMI's prohibition on log-callback reentry is an admissible-host obligation at
that boundary. See [the exact contract](../dev/fmi3/contracts.md#all-failure-helper-outcomes).
Grammar and generated artifacts are unchanged; the stage remains open.

The next nominal-query integration adds a mandatory complete public-call
contract for the actual emitted fragment/table/pool, alongside every earlier
adapter field and eventful literal-lowering guarantee. Successful storage and
the independently interpreted ordered XML state agree on the positive decoded
default 1; null, rejected lifecycle and invalid access cases include both
logging settings. The fixed checker kernel-proves actual signature membership.
All 33 new audit roots and affected packages pass in
`build/c-nominals/package-v2.log`; the required full `lake test` gate passed in
`build/c-nominals/full-gate.log`, with all 660 inventoried inputs unchanged.
Both actual archives are retained in `build/c-nominals/artifacts/`; their C,
header and GALEC members match `54618eb`. Valid memory, host
bindings, native ABI, allocation and remaining public-call obligations remain
explicit. See [the exact scope](../dev/fmi3/contracts.md#complete-nominal-queries).

The next state-access increment requires both actual getter/setter fragments,
their complete call behaviors and independent XML state ordering for the same
compiled Solve model and literal pool. It proves exact finite read/write values,
Model Exchange state refinement and memory frames, including all represented
error callback outcomes. Shared prefix and finite-domain lemmas support later
API proofs. All 39 additional roots and affected packages pass in
`build/c-state-calls/package-v1.log`; the required full artifact gate passed in
`build/c-state-calls/full-gate.log`, with all 667 inventoried inputs unchanged.
Both actual archives are retained in `build/c-state-calls/artifacts/`; their
C, header and GALEC members match `ca178d0`. Native storage/ABI, initialization
and remaining adapter obligations are still open. See
[the state contract](../dev/fmi3/contracts.md#continuous-state-getter-and-setter).

The derivative getter increment now requires its actual public and `model_rhs`
helper fragments, complete call contracts and independent XML derivative order.
The helper executes the existing numerical C statements of the same Solve model;
no derivative callback is assumed. `derivative_value_source` composes the existing
Flat/DAE/Solve relations to the exact Real derivative, and `derivative_source`
retains the actual numerical C contract alongside the adapter and literal pool.
Success, null handles, lifecycle/count/buffer errors and represented logging
outcomes are covered. The fixed checker proves numerical-name freshness for its
actual header candidates. All 41 added roots and affected packages pass in
`build/c-derivatives/package-v1.log`; the required full artifact gate passed in
`build/c-derivatives/full-gate.log`, with all 675 inventoried inputs unchanged.
Both actual archives are retained in `build/c-derivatives/artifacts/`; their C,
header and GALEC members match `035ad1d`.
No grammar, emitter or solver policy changes. See
[the derivative contract](../dev/fmi3/contracts.md#complete-continuous-state-derivative-query).

The Float64 getter increment requires the actual public fragment and helper,
independent XML numeric-reference lookup and complete prepared-call contracts.
The two counted loops validate all references before output writes and preserve
request order and duplicates. Nested derivative queries execute the same Solve
numerical C statements. Empty calls permit null arrays; invalid lengths/pointers
and references reach the actual error/log helper. Output and model-memory frames
are explicit. The request buffer reuses the tensor-memory specification without
adding array variables to the production grammar. All 58 added roots and affected
package checks pass in `build/c-float64-get/package-v2.log`. The required full
artifact gate passed in `build/c-float64-get/full-gate.log`, with all 686 inputs
unchanged. Both actual archives are retained in its `artifacts/` directory;
all C/H/ALG members match `8346cad`. Current state/time representation, complete initialization,
native ABI and remaining public APIs retain their existing open boundaries. See
[the Float64 getter contract](../dev/fmi3/contracts.md#complete-float64-getter).

The Float64 setter increment requires complete nonempty, empty and null calls,
all validation/lifecycle failures and represented logger outcomes. Every input
is validated before state writes; accepted binary64 payload bits are retained
exactly. A finite snapshot derived from original input storage connects the
last request to the semantic ME state update and a full memory frame.
Independent XML reference interpretation follows ModelStructure and the
derivative attribute to the same scalar local continuous state, with
initial=exact and reinit=false metadata. The fixed actual-file checker now
requires the printed setter and its one-table/pool contract alongside all
prior fields. All 51 new roots and affected package checks pass in
`build/c-float64-set/package-v1.log`. The required full artifact gate passed in
`build/c-float64-set/full-gate.log`, with all 694 source inputs unchanged.
Both actual archives are retained in `build/c-float64-set/artifacts/`; all C,
header and GALEC members match the published `636264f` outputs.
Initialization histories, native ABI,
ownership and remaining APIs keep the whole-stage claim open. See
[the setter contract](../dev/fmi3/contracts.md#complete-float64-setter).

The initialization increment changes the reviewed unit admission policy to a
finite start and an optional finite inclusive stop. Tolerance is unused by this
profile. The mandatory `InitializationCalls.FunctionContract` binds both actual
entry/exit fragments, typed complete-call behaviors, all represented failure
logging outcomes and their shared table/literal pool. Successful entry needs
writable clock storage, not initialized old clock values. The source consequence
uses the finite model value actually stored by default initialization or a host
setter and proves the unique Real trajectory at the supplied time origin.
Composition builds in `build/c-initialization/composition-v2.log`; all 51 added
roots and affected package checks pass in `build/c-initialization/package-v1.log`.
The required full artifact gate passed in `build/c-initialization/full-gate.log`,
with all 706 inventoried source inputs and the complete file set unchanged.
Both actual archives are retained in `build/c-initialization/artifacts/`.
Compared with `d519438`, only the initialization-entry body in `sources/fmi3.c`
changed; every other C/header/GALEC member is identical. The inclusive `atLeast_iff`
replaces the retired strict-order policy root; every other earlier root and the
axiom whitelist are retained. No source grammar is added. Allocation, arbitrary
host/lifecycle histories, remaining APIs and complete standards/ABI coverage
keep the stage open. See [the initialization contract](../dev/fmi3/contracts.md#complete-initialization-calls).

At the initial no-heap/RTOS review, the FMI emitter still used `calloc`/`free`.
The static-runtime checkpoint at the top of this document supersedes that
implementation: permanent multi-instance storage is now emitted. Complete
execution/ownership and transitive allocation contracts remain open; neither
initialization alone nor internal heap-frame invariants close them. MISRA C:2025 with the C11 profile has been
reviewed for initial findings; the 223-entry enforcement matrix is open.
Essential types, pointer guards, allocation and concurrency require
further proof and artifact coverage. Rule 15.5 is Disapplied; C11 is supported.
No MISRA compliance or approved deviations are claimed.
See [the rule review](../dev/standards-review.md#misra-c2025-and-static-storage-review)
and [K02–K05](../dev/roadmap.md#closure-checklist-before-grammar-growth).

The explicit-null increment supplies shared C null equality/inequality semantics
and independently checked printing for `((void *)0)`. It changes the actual
shared FMI instance guard and proves equivalence to its former implicit test
for every represented pointer. Literal-pool and interface-extension proofs
retain the distinction between a zero literal and an integer variable holding
zero. Comparisons between two non-null symbolic pointers remain unsupported.
Existing actual-function and artifact contracts remain required. The 44 new
roots retain every earlier root and the unchanged axiom policy. The required
full gate passed in `build/c-static-storage/full-gate.log`, including both
actual target archives with all 710 inventoried inputs unchanged. Only the
70 shared instance guards in the FMI adapter differ from `784f45b`; every
other C/header/GALEC byte is unchanged. Exact archives are retained in
`build/c-static-storage/artifacts/`. Other implicit pointer tests and whole
MISRA/adapter compliance remain open.

Its storage prerequisites prove preservation of supplied cell domains, types
and permissions through internal C execution, and bounded serial reservation,
exclusion and reuse of fixed slots. They do not establish a no-heap generated
product, native atomics, caller ownership or layout. At that checkpoint,
nested array/member addressing also required a structural correction before
the planned static instance array could support tensor fields; see MC10 in the
[standards review](../dev/standards-review.md#misra-c2025-and-static-storage-review).

The following subobject correction retains the containing array index at each
member selection and resets the selected member's local offset. Ten added
roots prove exact recovery of both index levels and the field name, tensor
region separation, arbitrary member-depth isolation and the actual typed
store's frame for a different record. All existing memory/call contracts and
affected C/FMI/eFMI/compiler package checks pass in
`build/c-static-storage/address-package-v3.log`. The required main artifact
gate passed in `build/c-subobjects/full-gate.log`, including both actual
target archives with all 711 inventoried inputs unchanged. Every C/header/GALEC
member is byte-identical to `b478606`; exact archives are retained in
`build/c-subobjects/artifacts/`. The ten new roots retain all earlier roots
and the unchanged axiom policy. No source grammar or Solve operation changes.
These are structural cell facts; native bounds, layout, effective types,
lifetimes and concurrent ownership require separate contracts. In particular,
they do not establish native pointer inequality for all different paths or
implement the planned static instance storage.

The next storage increment adds atomic Boolean cells whose ordinary heap
loads/stores are rejected. Their value conversion uses the existing Boolean
semantics; selected sequentially consistent exchange/store calls supply their
indivisible access rules. The bounded C reservation helper now has complete
fresh-parameter, initialization, loop, return and caller-continuation proofs.
Admitted entry cells imply termination and an exact sequential trace/result,
with bounded exchanges, memory frames and storage preservation. Its printed
function has the shared independent token/tree contract, including `_Bool`
and `volatile` type syntax. Successful scans refine the independent FMI slot
reservation; sequential exhaustion characterizes the supplied snapshot.
All affected packages and 38 added audit roots pass in
`build/c-atomics/package-check.log`; all earlier roots and the axiom policy are
retained. The required main artifact gate passed in
`build/c-atomics/full-gate.log`, with all 720 source inputs unchanged,
both actual target archives checked and every C/header/GALEC member
unchanged from `a1ceae5`. Exact archives and the comparison evidence are
retained under `build/c-atomics/`. Production still uses
`calloc`/`free`: the helper is not yet emitted into the FMI adapter. Native
atomic/header bindings, declarations, overlapping calls, ownership, reuse
initialization and complete factory/artifact composition remain open. These
proofs do not claim a globally full snapshot after a concurrent failed scan
or bounded native atomic latency. No source grammar or numerical IR changes.

The following identity increment replaces the factory's nested string-call
condition with an explicitly sequenced private helper. Null pointers reject
before any string access. With valid null-terminated buffers and the selected
library bindings, every helper call preserves memory and returns the independent
nonblank-name/token-equality predicate. The proof preserves arbitrary caller
observations and every sign-correct `strcmp` result. Its mandatory
`Identity.FunctionContract` binds the exact printed fragment, independent
tokenization and execution to the adapter's actual definition table. The fixed
checker also proves library-name freshness, and a consistent library environment
is constructed rather than assumed to exist. All earlier adapter fields remain
required. All affected package checks pass in
`build/c-factory/identity-packages-v1.log`, with 60 added audit roots and the
unchanged axiom policy. The required full artifact gate passed in
`build/c-factory/identity-full-gate.log`, including both actual archives and
the existing mutation/native boundary checks, with all 743 inputs unchanged.
The retained code-member comparison under `build/c-factory/identity-artifacts/`
shows only the new helper and its two factory call sites in FMI `sources/fmi3.c`;
numerical C and eFMI C/GALEC are unchanged from `00de05b`.

This increment also includes checked storage-frame and interleaving foundations
for the planned static instance slots. These describe the authored C scheduler
and an explicit ownership protocol; they do not establish a native scheduler,
weak-memory model or complete factory/history refinement. Production still
uses `calloc`/`free`. Native headers, libc implementation and hidden allocation,
caller-buffer validity, storage declarations, reuse initialization and the
complete creation/release calls remain open. No source grammar or numerical
IR case is added, and no whole MISRA/FMI/eFMI compliance claim is made.

The next factory-admission contract covers both public ME/CS entry points.
Parameter conversion constructs a fresh coherent environment; CS's unsupported
event/intermediate-variable guard runs before identity validation. Null identity
pointers need no string-storage/library premise. For valid caller buffers, the
independent nonblank-name/token-equality predicate selects the actual rejection
or creation suffix with unchanged memory and arbitrary later observations.
Rejection logging retains every represented foreign result, trace and writable
effect, including the no-outcome stuck case; disabled logging returns null with
the heap unchanged. The actual pool constructs all five identity/diagnostic
strings, whose readonly storage survives represented callback writes.

`FactoryAdmission.FunctionContract` is now mandatory in `AdapterContract`.
It binds both exact public signatures, independent function tokenization,
located fragments and prepared execution to the same emitted definition table.
The fixed checker kernel-proves signature membership. The actual-file source
consequence derives complete expected-token bytes from parsed identifiers,
without assuming a successful factory execution or a supplied local environment.
The C/FMI/eFMI/compiler package checks pass in
`build/c-factory/factory-contract-packages-v1.log`, with 50 added roots and no
removed roots or axiom-policy changes. The required full artifact gate passed
in `build/c-factory/factory-full-gate-v2.log`, with all 760 source inputs and the
complete file set unchanged. Both archives are retained under
`build/c-factory/factory-artifacts/`; their C/header/GALEC members match `13fb2a6`.
The first gate attempt rejected a failed signature-membership elaboration;
structural membership proofs fixed it without changing the contract or audit.
No emitter, source grammar, numerical IR or capability changes. Successful
creation, static-slot lifetime/reuse/release, private writable-cell callback
frames, native reentrancy/divergence, headers/ABI and MISRA closure remain open;
production still uses `calloc`/`free`.

The user-authorized driven input/state profile is being developed separately.
Its generated grammar, parser actions, tensor equation/initialization lowering
and mathlib matrix/storage bridge are checked, but it has no completed target
or actual-FMU certificate yet. The production compiler rejects it. The shared
tensor types preserve rank and shape, with array-backed storage; the original
unit-only register program remains a regression path. See the
[IR review](../dev/ir-review.md) for exact correspondence and remaining work.

The newly authorized array/AD slice has shape-preserving pointwise addition
and multiplication with array-evaluation proofs. `Tensor.Differentiation`
connects their JVP rules to mathlib `HasFDerivAt`, proves the VJP dual-pairing
identity, and proves the accumulated pullback and diagonal Jacobian of a
shared-input square. These mathematical Real operator proofs pass the core
axiom audit (`build/tensor-ad-package.log`). The array development frontend now
parses fixed `[2]` input/state arrays, `[2,2]` Jacobian outputs, one `.*` product
and ordinary two-argument calls. Decoder soundness/completeness, generated
recognition, name checks and exact call/operand source ranges pass the parser
audit (`build/tensor-parser-audit.log`). `jacobian` is selected by resolution,
not reserved by the lexer. `Array.Builtin` defines its mathematical meaning by
the derivative's action on every tangent, proves the matrix is unique, and
proves the diagonal result correct for the actual resolved square call at
every shape (`build/tensor-builtin-audit.log`). Typed Solve programs now contain
pointwise arithmetic. Their forward transformation preserves primal values and
computes a true Fréchet derivative; reverse execution retains forward values
and accumulates cotangents, with an adjoint theorem for the same derivative.
`Program.forward_derivative` and `Program.reverse_derivative` quantify over
arbitrary programs, shapes and differentiable entry-register functions. All
twelve new roots pass the unchanged axiom audit (`build/tensor-program-audit.log`).
The forward transform emits ordinary Solve instructions; the reverse evaluator
currently returns a saved pullback closure, not a statically lowered target
program. The array source now has separate Flat and DAE equation/initialization
semantics and lowering proofs. The actual partial residual solver is sound,
and complete for the two admitted development forms. Its prepared IVP executes
the RHS and initialization, with an optional dense Jacobian generated by
forward AD and a mathlib diagonal materializer. `ArrayProfile.lowering_chain_correct`
and `initialization_chain_correct` compose these edges over mathematical Real
values. `ArrayCompiler.prepare_correct` also binds the stored kernel to the
actual parsed source, its EBNF membership and its complete source equations.
The source-to-Solve checkpoint passed the complete local gate in
`build/array-source-full-gate.log` and
[CI for c4c4286](https://github.com/CogniPilot/rumoca_lean/actions/runs/34462561010).
The next numerical increment now specifies exact binary64 product rounding,
overflow rejection and signed underflow. `Solve.Tensor.Finite.executes_iff`
characterizes ordered finite program execution, including every intermediate
instruction. `Array.Finite` proves nearest-value bounds for the actual square
RHS and AD-generated Jacobian coefficients against their mathematical Real
values. These 26 new roots pass the core audit in `build/finite-array-audit.log`,
and the checkpoint passed [CI for 1413110](https://github.com/CogniPilot/rumoca_lean/actions/runs/34465555340).
The next C increment proves the complete counted helper bodies for addition
and multiplication over arbitrary tensor shapes. `CTensor.artifact_correct`
binds independently specified C tokens to all body behaviors, finite Solve
results and the whole-heap frame. Its eleven new roots pass the unchanged
axiom audit in `build/c-tensor-audit.log`. These helpers require finite inputs,
in-domain operations, valid readable input ranges, a separate writable output
range and a count fitting the authored 64-bit `size_t`. They do not prove
function-call ABI binding, scratch allocation, overflow/error paths or FMI
interaction. Static reverse transformation, whole-program C simulation and
tensor FMU/eFMU artifact certificates remain open;
[tensor-ad.md](../dev/tensor-ad.md) fixes the small scope. These development
parsers do not enlarge the production compiler's admitted source language.

The helper actual-file gate passed in `build/c-tensor-artifact-gate.log`.
`build/tensor-c/add-contract.log` and `mul-contract.log` audit the exact
file-literal contracts. The gate also rejects a changed loop bound and checks
native shared-input execution, output boundaries, signed underflow and empty
execution. It runs as `lake run tensor-c-test` and is included in `lake test`.
The complete gate passed in
[CI for 1007286](https://github.com/CogniPilot/rumoca_lean/actions/runs/34469374951).
These helper certificates do not establish the remaining tensor FMU/eFMU chain.

The subsequent call/fill increment strengthens the actual-file checker to
`CTensor.CallArtifactContract` for add/multiply and `CTensor.Fill.ArtifactContract`
for fill. It executes parameter conversions, fresh callee scopes, the actual
counted bodies and ordinary returns. `invoke_reaches` restores the exact caller
locals/types with the updated heap. A supplied definition-table binding and
header dictionary remain explicit; native linkage/ABI is not proved. Fill
preserves the exact finite value, including signed zero, and `solve_fill_correct`
identifies its result with the existing Solve initialization/seed program.
The three helper files passed `build/c-tensor-call-fill-gate.log`; all 21 new
roots pass `build/c-tensor-call-fill-audit.log` with the unchanged axiom policy.
The prior add/multiply body, finite and frame contracts remain conjuncts of the
stronger file proposition. The body-only limits above describe the earlier
checkpoint; ordinary calls are now covered, while whole-program allocation,
result storage, error policy and source-to-FMU composition remain open.
The required full gate for the call/fill increment passed locally in
`build/c-tensor-call-fill-full-gate.log` and in
[CI for e89e4f4](https://github.com/CogniPilot/rumoca_lean/actions/runs/34471779750).

The complete prepared-program increment introduces a shape-indexed storage
plan with one destination per tensor instruction. `CTensor.Lowering.emit_refines`
proves all behaviors of its actual sequence of C calls against independent
`Finite.Executes`, including intermediate operations, the exact result buffer
and preservation of every cell outside the planned destinations. Initial
storage must provide disjoint writable destinations, readable finite inputs,
stable pointer/count bindings and the explicit helper/header definitions.
Intermediate storage validity is derived by the proof, not assumed separately
for each call. `emit_code_count` proves one emitted call per instruction,
independent of tensor volume. The theorem starts at function-body entry;
allocation, the outer wrapper's argument binding and native linkage remain
separate obligations. This does not admit array models into production.

`TensorProgramSyntax` independently specifies scoped pointer/count parameters
and fill/binary calls. `render_denotes` structurally certifies the printer for
arbitrary valid names and instruction lists. `Lowering.ArtifactContract` binds
that complete text to the emitted body and its finite execution theorem.
The fixed development file adapter checks the actual AD-generated square
coefficient program, universally over tensor shapes, with an explicit result
parameter. Its exact root passes `build/tensor-c/program-contract.log`; all 22
added audit roots and the actual-file/native gate pass in
`build/c-tensor-program-gate.log`. A changed add-to-multiply call is rejected.
The native check additionally requires external helper declarations; header
preprocessing and native linkage are still boundary checks. The full repository
gate for this increment passed in `build/c-tensor-program-full-gate.log` and in
[CI for 08b8a7d](https://github.com/CogniPilot/rumoca_lean/actions/runs/34476481293).

The next increment closes the authored outer-function entry and return:
`Lowering.program_call_refines` proves every complete call behavior against
`Finite.Executes`, with exact result storage and the whole memory frame.
Parameter conversions and fresh scope binding are derived from the independent
signature validity rules. `Lowering.CallArtifactContract` adds this guarantee
to the existing text/body proposition. The fixed program-file checker also
requires `ProgramFixture.Entry.StorageContract`: for the actual square
coefficient program, named input and scratch objects establish all required
readability, writability and separation invariants. It quantifies over arbitrary
shapes and finite input values, subject to the count bound and ordered finite
execution. The symbolic initial heap is supplied storage, not a verified
allocator or native ABI layout. External helper/header definitions remain
explicit. These call/storage proofs do not establish tensor FMI admission,
overflow/error handling or complete source-to-FMU composition.

All 34 added call/storage roots pass the unchanged axiom audit in
`build/c-tensor-entry-gate.log`. That gate also passes the stronger actual-file
certificate, operator-mutation rejection and the existing native boundary check.
`build/tensor-c/program-contract.log` audits the exact file theorem with only
`propext`, `Quot.sound` and `Classical.choice`. The required full gate for this
increment passed in `build/c-tensor-entry-full-gate.log` and in
[CI for 6d4ec7c](https://github.com/CogniPilot/rumoca_lean/actions/runs/34479402664).

The diagonal output helper now has `CTensor.Diagonal.ArtifactContract`. It binds
the complete actual C text to ordinary call entry, the existing zero-fill call,
every diagonal copy and return. `ExecutionContract` requires exact coefficient
bit patterns on the diagonal, positive zeros elsewhere, and preservation of
every cell outside the output matrix. `SolveContract` identifies the result
with the prepared `Solve.Tensor.DiagonalProgram` after its coefficient program
has executed. All statements quantify over arbitrary tensor shapes, including
empty ones, with separate readable coefficients and a writable matrix range.
The matrix cell count must fit the authored 64-bit `size_t`; the dimension,
stride and every unsigned update are proved to fit from that single bound.
The unsigned-addition rule follows C11 N1570 §6.2.5's modulo semantics.

All 35 added roots and the actual-file/native gate pass in
`build/c-diagonal-gate.log`. `build/tensor-c/diagonal-contract.log` audits the
exact file theorem. One assertion group extends the existing native AD fixture
to its dense matrix output; no additional example model or rejection matrix
was added. The full gate passed in `build/c-diagonal-full-gate.log` and in
[CI for 8a3b902](https://github.com/CogniPilot/rumoca_lean/actions/runs/34483284726).
This helper checkpoint does not compose coefficient production and diagonal
output into the actual whole model function. FMI storage/metadata/lifecycle binding,
overflow/error policy and tensor source-to-archive certificates remain open.
External header/linkage and valid object-storage assumptions remain explicit;
there is no new allocation or native ABI theorem.

The composed Jacobian function now has `Lowering.DiagonalArtifactContract`.
`emitDiagonal_correct` composes the coefficient program with its prepared
diagonal output; `diagonal_call_refines` covers every complete function-call
behavior. The result contains the exact finite Solve matrix and preserves the
coefficient buffer and every cell outside the combined destinations. Reserved
matrix storage remains writable throughout coefficient execution. The printer
supports the explicit diagonal call through independent token rules, and
`emitDiagonal_code_count` retains one call per prepared tensor operation.

`ProgramFixture.DiagonalEntry.StorageContract` discharges the generic storage
premises for the existing square/Jacobian example, universally over shapes,
finite inputs and backing heaps. Its complete-file contract replaces the
coefficient-only development artifact; no new source model or grammar case is
admitted. Ordered finite coefficient execution, a matrix count fitting `size_t`,
supplied object storage and external helper/header bindings remain explicit.
This proves the Jacobian function, not the complete IVP or FMI lifecycle.
Its 23 added roots and the actual-file/native gate pass in
`build/c-diagonal-model-gate.log`. The exact file theorem is audited in
`build/tensor-c/program-contract.log`; the required full gate passed in
`build/c-diagonal-model-full-gate.log` and in
[CI for f63d69a](https://github.com/CogniPilot/rumoca_lean/actions/runs/34487668082).

The next increment constructs C functions through `Lowering.Named` and groups
them in `PointwisePlan`, indexed by one prepared `Solve.PointwiseIVP`.
`Named.emit_correct` proves structural correspondence to the existing emitter,
including the result buffer. `PointwisePlan.correct` composes the complete-call
and independent printer contracts for initialization, RHS and the optional
diagonal observation. It requires unique entry names and excludes helper-name
collisions. Shape/count metadata remains attached to the target buffer plan;
no tensor coordinates, differentiation decisions or solver policy are introduced.

The fixed IVP artifact adapter reads all three actual C members of the existing
square/Jacobian example. Its proposition retains the complete Jacobian storage
contract and adds initializer/RHS storage contracts over arbitrary shapes,
heaps and finite input values. These derive argument binding and the lowerer's
storage predicates from readable input and writable output ranges. Initialization
produces the prepared IVP's exact zero state; RHS execution yields the independent
finite Solve result. Each call preserves every cell outside its output range.
All 22 added roots and the actual-file/native gate pass in `build/c-ivp-gate.log`.
`build/tensor-c/ivp-contract.log` audits the exact three-file theorem. The
required full gate passed in `build/c-ivp-full-gate.log` and in
[CI for e1a734b](https://github.com/CogniPilot/rumoca_lean/actions/runs/34491283172).

`CCalls.Typed` now executes the same typed tensor loop bodies with ordinary
return values, saved local types and call destinations. `loop_step` and
`loop_reaches` embed successful `CLoops.Calls` executions into this machine.
`append_reaches` carries a closed execution into an arbitrary caller context;
only the old terminal step becomes a zero-step transition. `CallResult`
requires both contextual completion and an exact standalone behavior, excluding
stuck or divergent outcomes under the existing finite-execution premises.
`invoke_return_reaches` composes the actual call statement with its caller's
return expression and conversion. It does not assign a meaning to an FMI name.

`ProgramEntry.Contract` and `DiagonalEntry.Contract` retain their previous
printer/call/storage contracts and additionally require `TypedCallCorrect` and
`TypedDiagonalCallCorrect`. The fixed three-file IVP checker therefore certifies
the emitted functions under the typed, value-returning machine too. These
theorems preserve the exact finite Solve result and whole-heap frame for all
shapes, with the same explicit storage and header/definition-table premises.
All 22 added roots, the stronger actual-file certificate, mutation rejection and
the existing native boundary check pass in `build/c-typed-gate.log`. The exact
file root is audited in `build/tensor-c/ivp-contract.log`; the package build
passes in `build/c-typed-package.log`. No new source model or native test matrix
is introduced. The required full gate passed in `build/c-typed-full-gate.log`
and in [CI for 2e53e66](https://github.com/CogniPilot/rumoca_lean/actions/runs/34494402729).

These remain instantaneous C contracts. The existing FMI body proofs must still
be connected to the typed machine's statement/scope rules and composed with
the actual tensor wrappers. Instance storage/metadata, overflow/error policy,
lifecycle/time behavior and source-to-FMU/eFMU composition remain open. There
is no allocator, native ABI or machine-code theorem. Production source admission
and the README are unchanged.

`Source.Solves` is the ideal continuous reference ODE over mathematical reals,
not a complete operational interpretation of the predefined Modelica Real
class. MLS 3.7 §4.9.1 requires finite stored Real values; this implementation's
stored-value contract is the separate binary64 numerical profile. Refinement
to an unbounded ideal trajectory does not claim that such a trajectory is
itself a sequence of valid stored Real values.

For the tracked path beyond this baseline, see [the roadmap](../dev/roadmap.md).
The newly authorized eFMI unit profile and its standards review are tracked
in [the eFMI roadmap](../dev/efmi.md). Its DAE-derived GALEC product and tensor
Solve algorithm are separate from the numerical IVP path. The Algorithm Code
contract binds actual `.alg` and both EBNF files to the source/DAE and Solve
refinement proofs. `ProductionContract` extends this with the actual complete
C member, its object-memory execution and legal serial interaction traces.
`ManifestContract` extends the code contract to the three actual XML documents,
their checked identity fields, checksum/reference construction, and decoded
mappings to C execution.
`ArchiveContract` composes the manifest contract with the complete stored-ZIP
byte grammar for the same five code/XML strings and all 45 pinned schema
resources. `compile_archive_verified` proves this contract for every successful
compiler/`Artifact.efmuArchive` result. The fixed actual-file checker constructs
`Rumoca.CheckedEFMIFiles.source_to_archive` from the complete archive bytes,
source and both grammars. Its full gate passed in
`build/efmi-archive-full-gate.log`, with only the usual three axioms. These
contracts do not certify a physical lifecycle scheduler or full eFMI standards
conformance.
The schema/text discrepancies in the pinned
eFMI 1.0.0 Beta 1 draft remain explicit review items.
The source parser and EBNF tooling live in the independent
[parser package](../packages/parser/README.md); compiler and target proofs
depend on its public runtime and proof modules. Shared IR and arithmetic live
in [core](../packages/core/README.md); C generation and target contracts live
in [backend-c](../packages/backend-c/README.md), with FMI interfaces in their
respective backend packages. The
[compiler package](../packages/compiler/README.md) composes their proofs.

## Required gate and actual-file binding

Run `nix develop .#verification --command lake test`. This checks Lean proofs,
grammar freshness, axiom dependencies, actual source/C contracts, mutation
rejection and native C execution. `lake build audit` alone is insufficient.

For development, each package has a separate cached check library; see
[incremental checks](development.md). The `#audit axioms` command rejects
unapproved dependencies during Lean elaboration. Lake reuses that checked
module only while its source and import dependency traces remain current.
The complete gate retains all former audit roots and actual-file checks;
reusing package proofs does not cache a certificate for different artifact bytes.

The independent [SHA-1](../packages/sha1/README.md) and
[XML](../packages/xml/README.md) packages own their implementations, proofs and
axiom audits. They use Lean's standard library, with the local verification
tooling for their checks. The backends own model-specific documents and the
compiler composes actual-file certificates. Extracting these packages does
not extend the manifest/archive contract or establish full standards compliance.

Prioritize general formal theorems over accumulating example tests. Keep a
small set of integration checks for the trusted file adapters, external format
compatibility and native compilation. Do not add case matrices that merely
repeat behavior already quantified over by a theorem. These boundary checks
support the proof infrastructure; their count is not a measure of verification.

To verify another source within the same grammar:

```sh
nix develop .#verification
lake build
bash scripts/verify-artifact.sh path/to/Model.mo build/checked-model
```

The output directory contains a source snapshot, emitted C, a fixed checking
entry point (`Artifact.lean`), a readable producer-supplied `Candidate.lean`,
an axiom report and a SHA-256 manifest. Hashing records files; it is not a proof.
`Rumoca.ArtifactCheck` independently reads the actual source and C files,
quotes them as Lean literals and constructs the fixed proposition:

```lean
Generated.source = actualEbnf ∧
  ∃ a : Artifact source, compile source = .ok a ∧ ArtifactContract a emitted
```

The kernel checks this proposition; the adapter audits the dependencies of
that exact theorem. It never executes producer-supplied Lean commands or
accepts their theorem statements or audit text as authority. `Candidate.lean`
is for inspection/export only. The small file-to-proposition adapter, file I/O
and fixed checking entry point are explicitly trusted infrastructure. To run
that entry point directly, set `RUMOCA_SOURCE` and `RUMOCA_C` to the actual files.
It also reads the actual EBNF file (`packages/modelica-parser/grammar/Modelica.ebnf` by default, or
`RUMOCA_GRAMMAR`) and kernel-checks equality to the certified grammar source.
An early native comparison rejects a mismatched grammar; it cannot authorize
an artifact. The successful certificate proves equality of the actual and
embedded literals by kernel reflexivity, avoiding redundant UTF-8 evaluation.

## Parser and pass contracts

The new located frontend adds source-indexed UTF-8 spans without admitting
grammar cases. `Aligned` checks exact token slices, all trivia gaps, order
and disjointness. Generic LALR annotation preserves terminal/production
identity, covers children including epsilon nodes, and checks leaf ranges
against the input. `LocatedParsed.erases` retains the production parse result.
`Source.attach_complete` now proves completeness from an independent token
spelling/trivia relation, using Lean's standard UTF-8 cursor and iterator
libraries. `Rumoca.Lexes.spelled` discharges that relation for the actual
Modelica lexer. `Parsed.parseLocated_eq` and `parseLocated_complete` identify
the total located frontend with the same accepted source syntax. `Artifact`
requires a located parse; the compiler's retained `compile_complete` has no
extra location-success premise. The actual-file certificate adapters use the
same total construction. These 14 new roots pass the existing package audits
in `build/located-provenance/package-gate.log`; the required complete gate
passed in `build/located-provenance/full-gate.log`, including actual C, FMU and
eFMU certificates and existing boundary checks.
The subsequent generic LALR annotation completeness proof is described below;
origin preservation through the complete IR/printer pipeline remains open. See
[the provenance contract and roadmap](../dev/provenance.md).

The next provenance foundation adds a generic checked origin array, mandatory
nonempty parent records and a proof that every origin reaches a source leaf.
The fixed Modelica field table has exact file/AST-field lookup and production
boundary proofs; configurable-scanner attachment completeness is instantiated
for GALEC as well. These 23 new roots pass the package audit in
`build/origin-tables/package-gate.log`; the required full gate passed in
`build/origin-tables/full-gate.log`, including both actual target archives.
The source table is not yet required in every semantic IR, and no emitted-byte
origin map is certified by this increment.

`Parallel.map_eq` proves equality to sequential mapping for every pure analysis
function, input list and job budget, using Lean's standard logical `Task`
semantics. Batch results retain file identity, source snapshots and input
order. Native task scheduling and file reads are infrastructure, not a proved
OS concurrency implementation. The CLI's file reads are currently sequential.
The separate LSP reuses structured source diagnostics and converts their ranges
to UTF-16 with Lean's library. Terminal context rendering, LSP transport and
file-map conversions are tested presentation/infrastructure boundaries.

Name-resolution errors carry a primary span plus a related declaration span
in the same immutable source. `LocatedParsed.resolve_error_locations` proves
that each failing resolution points to the actual erroneous occurrence and
its declaration, with the exact AST-field text at both ranges. End-name errors
retain precedence over derivative-name errors. `resolve_complete` proves that
the enriched diagnostics retain every successful resolution. CLI JSON, context
notes and LSP related information consume this same data. The LSP respects
the client's related-information capability; `diagnostics_without_related`
proves those extra locations are omitted when support is disabled. The three
new roots pass the unchanged axiom audit, and the existing real LSP/parallel
frontend checks pass in `build/diagnostic-locations-frontend.log`.
The required full local gate passed at `df382d0` in
`build/diagnostic-locations-full-gate.log`, including FMI ME/CS and the complete
eFMU artifact gate. This is evidence for the unchanged authored contracts.
Compiler failure-only reparsing has now been removed: the driver returns
structured located diagnostics directly. Later IR/printer provenance remains
open; these diagnostic theorems do not close those obligations.

The [airborne assurance plan](../dev/airborne-assurance.md) records additional
requirements, traceability, independent review, target integration and tool
credit work. No current theorem establishes DO-178C compliance.

The independent `Lexes` relation specifies maximal-munch Modelica lexing.
`lex_correct` proves soundness and completeness. Source length plus one is
sufficient fuel. The token parser is sound and complete for the exact 16-token
model form. `Parsed` binds an AST to the source characters with erased proofs.
`compile_complete` proves successful compilation for every syntactically valid,
resolved tiny model.

The source frontends now use the same generated LALR parser. The old DFA
runtime, regular-expression expander, duplicated runtime tables and generator
have been removed. Successful source EBNF lowering is checked against independent
recursive expression semantics. Alphabet reflection includes unknown symbols,
which encode outside the terminal range and distinctly from EOF.

The EBNF reader accepts comma/equal and selected Rumoca/parol-style colon
notation, single/double quoted literals and implicit sequences. The embedded
reader result is kernel checked and actual grammar files must match the embedded
source. Independent character and token relations now specify this dialect;
`EBNF.parse_iff` proves exact agreement with the public text reader, including
its actual input-size budgets. `parse_rejected_iff` characterizes all rejected
source strings. Forty added generic roots pass the parser package audit in
`build/source-cutover/build/ebnf-reader/parser-package.log`. The generated
ordinary and located parser contracts now include independent source notation.
`Frontend.compile_correct` also composes that notation with CFG preservation.
Both language package audits and existing integration checks pass in the same
directory's `language-packages.log` and `integration.log`. The required main
artifact gate for P02 passed in `build/ebnf-reader/full-gate.log`, with all 591
inventoried inputs unchanged. Both actual target archives and their hashes are
retained in `build/ebnf-reader/artifacts/`. No full ISO 14977 theorem or exact
error-message contract is claimed.

The in-tree `Parser.LALR` candidate generator implements
canonical LR(1) construction and LR(0) kernel merging. `LALR.parse_sound` proves
that every successful checked parse tree derives the exact input in mathlib's
CFG semantics, universally over tables and fuel. `LALR.RuntimeProofs.run_checked`
also proves that raw execution preserves valid trees and the exact input word,
so a returned tree cannot fail the public parser's final check.

`LALR.Safety.validated_parse_safe` proves that tables passing the independent
finite structural validator cannot produce internal table or tree errors, for
any input and fuel. Checked edge annotations cover every actual shift and goto;
a backwards calculation verifies reductions for every represented stack path,
including unbounded recursive paths. The generated Lean module contains the
actual tables, edge annotations, a kernel-checked `safety_checked` proof and its
universal `execution_safe` consequence. Candidate generation is not assumed
correct. Shared reduction/acceptance summaries avoid recomputing them for each
table entry; `validate_iff` connects the implementation to its obligations.
The emitter checks each reduction summary in its own theorem and substitutes
the proved array equalities into this unchanged validator. Private proof-only
snapshot definitions add no runtime parser storage. Both emitted language
instances and the existing corruption controls pass
`build/tensor-sharded-lalr-gate.log`; this changes certificate evaluation, not
the parser's semantic contract.

`LALR.FirstCheck.validate` independently checks nullable/FIRST closure for every
grammar production. `FirstProofs.nullable_complete` and `first_complete` prove
that those facts cover every empty derivation and every derivable leading
terminal in mathlib's CFG semantics. `lookahead_complete` covers the actual
lookahead calculation used by LR closure, including a caller's lookahead after
an empty suffix. These results do not assume that the generator's fixed-point
search is correct. `lalrgen` emits the actual fact array, a kernel-checked
`first_checked` proof, and universal `nullable_coverage`/`lookahead_coverage`
corollaries. The certificate uses Lean's proof-producing `cbv` normalizer for
standard-library sorting equations; its terms are kernel checked and axiom
audited. No native-reduction axiom is introduced.

The facts may conservatively include extra nullable marks or terminals, so this
is a coverage contract, not an exact FIRST-set computation theorem. Regressions
reject missing direct/transitive predictions and nullable marks, wrong array
sizes and EOF in the grammar's terminal sets. Another regression permits a
conservative summary while proving that its nullable mark does not imply the
grammar accepts the empty word.

`LALR.ItemCheck` now checks the initial augmented item, closure, advances through
actual shifts/gotos, completed reductions and EOF acceptance. For every grammar
and table instance satisfying that validator, `Completeness.accepts_iff_parse`
proves CFG acceptance iff the actual parser accepts at some finite fuel.
`Grammar.accepts_tree` constructs the existential derivation tree from mathlib's
semantics; `Completeness.parse_tree` follows it with exactly one interpreter
transition per tree constructor plus EOF acceptance. These are universal
theorems, independent of the generator and frontend. The package proof/audit
gate passes in `build/lalr-cutover/build/completeness-audit.log`.

`LALR.Fuel` and `LALR.Progress` additionally validate grammar/state credits and
prove a strict potential decrease on every interpreter transition. Their
linear input-size bound guarantees that every word finishes with either a
correct tree or syntax rejection. Grammar membership is equivalent to success
at that same bound, and malformed inputs cannot cause internal errors or
exhaustion. The complete parser package audit passes in
`build/lalr-production/progress-audit.log`, under the unchanged axiom policy.
Both emitted grammar instances and the existing recursive/mutation controls
pass in `build/lalr-production/resource-integration.log`.
The generated entry-point and exact returned-tree contracts also pass the GALEC
audit in `build/lalr-production/entry-contract.log`. The required full root
artifact gate passed in `build/lalr-production/full-gate.log`, including both
actual target archives and the existing rejection/native controls. All 578
inventoried inputs remained unchanged throughout the run. State/item credit
arrays are proof-only; runtime fuel uses two scalar coefficients. These results
do not prove candidate-search convergence for every conflict-free LR grammar,
or wall-clock/heap performance.

The EBNF preservation increment adds independent recursive expression
semantics and a finite structural lowering certificate. Universal soundness
and completeness connect those semantics to mathlib CFG derivations, including
empty forms, named recursion and finite alphabet reflection. The public
`Frontend.lower_correct` and `compile_correct` cover successful preprocessing;
the latter binds the exact reader result. Generated `source_parse_correct`
combines a kernel-checked read of the embedded EBNF text, its expression-to-CFG
witness, acceptance equivalence and all-input bounded LR termination. The
proof-only witness is not retained by runtime token parsing.

The 19 added generic audit roots and parser packages pass in
`build/ebnf-stage/build/ebnf-package-staged.log` (796 jobs). Actual Modelica,
GALEC and recursive certificates and the existing mutation controls pass in
`build/ebnf-stage/build/ebnf-integration-staged.log`. Source-reader checking
reuses the exact character-view certificate and separately checks lexing and
expression parsing. The EBNF increment's required main artifact gate passed in
`build/ebnf-preservation/full-gate.log`, with all 584 recorded inputs unchanged
and both actual target archives retained under its `artifacts/` directory.

The subsequent source cutover supplies `LALR.TokenParser.Actions`: builders
receive the actual concrete tree and original token payloads, and specify an
independent relation between tokens and their chosen AST. The generic
`parseWith_iff` proves soundness and completeness for that relation;
`parseWith_execution` retains the actual LR result and checked tree. It neither
requires a grammar-shaped AST nor requires every AST to reconstruct a unique
token spelling. The current language-owned exact-token decoders instantiate
this interface without becoming the generic parser.

Generated one-step named-rule equations let Modelica and GALEC prove AST token
membership directly in EBNF semantics. Unit, driven and array cases use these
derivations, not execution of empty-name token patterns. GALEC also uses the
certified generated bound instead of its former fixed fuel expression. Modelica's
`parseTokens_iff`, character binding, located-source and compiler completeness
contracts are retained. Actual-artifact source membership now names independent
`EBNF.Accepts sourceGrammar`; all numerical and emitted-file fields remain.

The initial Modelica parser/action modules pass in
`build/source-cutover/build/modelica-actions.log` (770 jobs), and the GALEC package
passes in `build/source-cutover/build/galec-cutover.log` (780 jobs). The final parser package gate passed in
`build/source-cutover/build/parser-cutover-gate.log` (1525 generic/generator jobs,
806 language jobs). The downstream package audits, freshness, LALR corruption
controls, native compiler/C execution and LSP/parallel boundaries passed in
`build/source-cutover/build/downstream-cutover-v2.log`. This also fixes an
import-related Lean keyword collision by renaming an internal eFMI metadata
list; emitted manifest values are unchanged. The direct actual-source/C contract also passed in
`build/source-cutover/build/actual-c-cutover.log`. The required complete
actual-artifact gate passed in `build/lalr-source-cutover/full-gate.log`, with
all 581 recorded inputs unchanged throughout the run. Actual FMU/eFMU archives
and their hashes are retained in its `artifacts/` directory. This covers the
existing actual-source/C, FMI ME/CS, GALEC, complete eFMU and rejection/native
boundaries. These are implementation checkpoints, not a completed compiler
or FMI/eFMI compliance claim. Richer LR rejection reporting and generator
success/cost proofs remain open;
see [LR01–LR07](../dev/lalr-parser.md).

`LALR.LocatedCompleteness` now proves exact token/span preservation for arbitrary
tree fragments, including nullable nodes. Every successful raw parse has a
located result for the same tree. `parseLocated_erases` preserves the exact
success/error result; `parseLocated_correct` composes table and progress
certificates into complete located parsing at the same bound. Generated entries
choose that bound automatically and compose EBNF membership and reader-result
binding. A shared scalar `fuelForLength` avoids mapping a list solely for its
length. Spelling/trivia remains the frontend lexer's responsibility.
Eight generic and six emitted Modelica/GALEC roots pass the unchanged axiom
policy in `build/source-cutover/build/lalr-locations/language-packages-v2.log`.
Freshness and existing recursive/mutation checks pass in its `integration.log`.
The required main artifact gate for this span increment passed in
`build/lalr-located/full-gate.log`, with all 582 inventoried inputs unchanged.
Both actual target archives and their hashes are retained in
`build/lalr-located/artifacts/`; the existing C, FMI ME/CS, GALEC and eFMU
boundary and mutation checks passed.
No grammar or numerical behavior is added.

Source-indexed IRs retain their predecessors. State/register indices cannot
refer to absent values. The public per-pass contracts in `packages/compiler/Rumoca/Lowering.lean`,
`packages/backend-c/RumocaC/Lowering.lean` and the target semantics are:

| Pass | Theorem | Meaning |
| --- | --- | --- |
| AST → Flat | `Flat.lower_correct` | Equivalence of the named source equation and indexed flat equation |
| Flat → DAE | `DAE.lower_correct` | Equation holds iff its residual is zero |
| DAE → Solve | `Solve.lower_correct` | Residual is zero iff the derivative equals the solved RHS |
| Solve → C expressions | `C.lower_correct`, `C.lower_binary64_correct` | Ideal RHS preservation and exact rounded step preservation |
| C program → text | `CSyntax.module_render`, `lower_correct` | Rendered text denotes the target in an independent grammar |
| Solve → C statements | `CStatements.lower_correct`, `lower_behavior_correct` | Statement execution and all observable behaviors preserve finite Solve/source-profile semantics |

`lowering_chain_correct` explicitly composes the first four contracts.
The numerical policy and callable vocabulary live in shared `RumocaCore.Profile`;
`Rumoca.Source` imports no backend. `Profile.AdmitsUnit` requires the complete
derivative solution set to be `{1}` before licensing the fixed unit-step policy.
`Profile.behavior_congr` transports this condition and relational rounding
through equation equivalence. `Flat.behavior_correct`, `DAE.behavior_correct`
and `Solve.behavior_correct` lift each real pass;
`CStatements.solve_behavior_correct` supplies the target execution edge.
`CStatements.lower_behavior_correct` composes these in the artifact and driver
theorem. This is a policy for the frozen equation, not an arbitrary ODE solver
or general partial-pass simulation framework.
`Solve.lower_samples_correct` connects execution of the actual register
program to the independent relational source sampling policy. Proof-carrying
IR invariants are checked by the kernel; they are not added axioms.

## Shared C package and header bindings

`packages/backend-c` owns numerical C emission, the structured C tree,
object-memory and call semantics, the finite-addition extension, and thin
emission of tensor Solve algorithm instructions. It depends on core and the
proof audit tooling, with no dependency on either FMI backend or the compiler.
Both FMI backends depend on it and keep their respective wrappers, metadata
and complete-output contracts.

The routes remain DAE → GALEC → Solve → C for eFMI and DAE → Solve → C for
FMI 3. GALEC text branches from the same checked GALEC IR that is refined into
Solve. The existing tiny numerical and algorithm Solve representations are
still distinct; a shared package is not a proof that they are interchangeable.
The backend does not read GALEC text, redo DAE lowering or select a solver.

`CInterface` supplies named constants and declared C types to `CBody`,
`CCalls` and `CArithmetic`. Shared proofs quantify over this dictionary.
Each adapter installs a private local instance of its concrete header bindings;
imports install no global default. The actual compiler contracts select those
concrete bindings. eFMI type aliases are looked up in the rendered header's
declaration nodes. `CHeader.interface_alias` and `interface_return` prove the
shared interpreter's alias and return conversion agree with those declarations
for every scalar/value. These facts are fields of the actual header contract.
The meanings of primitive C types and the physical ABI retain the existing
reviewed platform boundary.

## C syntax and statement execution

`CSyntax.Denotes` specifies the emitted declarations, expressions, loop guard,
assignment and unsigned decrement through independent lexical/token rules.
`expression_render` is structural over arbitrary expressions; `module_render`
proves text denotation for every module in this syntax profile. It composes
lexical constructors directly, without executing a C reader. `denotes_unique`
proves that the same text cannot denote two different target programs.
The actual-file certificate still requires exact equality to the rendered
bytes. The header is an exact prefix; preprocessing and standard headers
remain reviewed infrastructure rather than implemented C semantics.

`CStatements` is the target semantics used by the high-level theorem. It has
statement constructors for assignment, unsigned decrement, sequencing, while
and return, with explicit local bindings, call entry and a continuation of
remaining statements. Each assignment, decrement and control operation takes
a separate transition. A missing binding is stuck: `rhs(void)` has no `x`
parameter. `lower_scoped` proves compiled bodies use only bound variables.
`denotes_statements` relates emitted characters to the statement AST's independent
token grammar. Expressions have no side effects, so evaluation order has no
observable effect in this profile.

The countdown is `Fin (2^64)` and unsigned decrement is modular subtraction.
`decrement_positive` proves it equals natural subtraction when positive; the
loop proof applies it after the nonzero guard. Every local counter is in range
by its type. The earlier `CExecution` whole-iteration machine remains with its
own execution proofs for existing contracts; it is no longer the final
operational boundary. No simulation between these two machines is currently
proved. Retiring it or proving that relation is tracked as C02.

`Transition.Machine.Behaves` distinguishes returned results, infinite execution
and stuck execution. `CStatements.behaviors_correct` proves every behavior of
each exported function is the exact finite Solve result. `all_terminate`
excludes infinite reductions. `all_complete` shows every reachable state can
finish with that result. These functions have no external calls, pointers,
volatile accesses or I/O, so observable behavior consists of termination and
the returned encoding, without an external-event trace.

## Whole-compiler theorem

`compiler_semantic_preservation` quantifies over successful compilation,
actual emitted bytes, every finite IEEE bit pattern, every uint64 count,
every exported function and every behavior. It proves the emitted text denotes
a scoped target whose behaviors are equivalent to the independent relational
`Source.SampledBehavior` semantics:

```text
compile source = ok artifact → artifact.cSource = emitted →
  ∃ targetC, Denotes emitted targetC ∧ WellScoped targetC ∧
    ∀ function bits count behavior,
      CBehaves targetC (call function bits count) behavior ↔
      SourceSampledBehavior artifact.source function bits count behavior
```

Consequently every target behavior is an allowed source-profile behavior,
and neither divergence nor stuck execution is possible. This is behavioral
preservation at the C boundary. The proof uses deterministic finite execution
and relational composition, not CompCert's general small-step simulation
framework for an optimizing C-to-assembly compiler.

`compile_verified` supplies the source/byte contract, behavior equivalence,
scoped statement syntax, termination/completion of every call,
original-symbol EBNF membership and refinement against any real source
solution. The actual-file checker checks the whole `ArtifactContract`.

Exact preservation is against the explicitly rounded numerical profile.
It would be false to claim binary64 results always equal the mathematical
real trajectory. Numerical refinement is a separate theorem.

`compiler_preserves_property` transfers any predicate of source-profile
observations to every behavior of the actual parsed output. It is derived
from `compiler_semantic_preservation`; it does not require a separate
assumption about target behavior.

The initial ME-within-CS internal contract lives in
`RumocaCore.Solve.ModelExchange`. The ME kernel owns continuous state and
derivative evaluation; `UnitSolver` consumes it; `CoSimulation.State` contains
the ME state and an exact count of completed unit steps. `run_model_correct`
and `run_progress` relate repeated solver calls to finite Solve execution and
the time grid. `ArtifactContract.model_exchange` and `co_simulation` bind the
current scalar C exports to those internal model/solver semantics.
They do **not** assert an FMI ABI, Float64 communication-time semantics,
instance-memory/lifecycle correctness or an FMU package. Those proof obligations
remain F01–F04 in the roadmap.

## FMI archive and runner

The unit profile now has a Lean FMU producer and a separate Lean runner
package reusing FMPy. `rumoca MODEL.mo -o MODEL.fmu` emits model/build XML,
an internally linked numerical `sources/model.c`, a structured C ABI adapter in
`sources/fmi3.c`, and a host Linux shared library exposing ME and CS. Before
native compilation it invokes the fixed actual-file checker on the staged
Modelica source, current EBNF, numerical kernel, adapter and both XML files, then audits
the result.
ZIP and FMPy validation run before an atomic publication rename. Failure
leaves a previously published FMU intact. Toolchain I/O and publication are
tested infrastructure, not verified filesystem operations.

`Build.recipe` supplies both the native compiler invocation and the source-build
XML for Linux x86_64/aarch64 GCC. `Build.ArtifactContract` requires valid XML
characters, a uniquely decoded recipe for each platform, the explicit C11 and
floating-point options, the single compiled `fmi3.c` source and the environment's math library.
That translation unit includes the private numerical `model.c`.
The independent `RequiredInvocation` also checks the producer's argument list,
universally over its path arguments. `FMI3.SourceBuildContract` composes this
with the unchanged numerical `ArtifactContract`. The fixed
`CheckFMI3Build.lean` adapter reads actual files from a single supplied directory
and reuses the XML package's compositional character certificates. A missing
declared library is rejected before native compilation.

Six new roots pass the unchanged axiom audit in `build/fmi-build-package.log`.
The actual-file, schema, native and mutation gate passes in
`build/fmi-build-artifact-gate.log`; the packaged `kernel-audit.log` contains
the fixed `Rumoca.CheckedFMI3Files.source_to_build` root.
The existing source-rebuild check validates the official build-description XSD,
reads compiler/options/sources/libraries from that XML, and resolves the resulting
binary in a fresh loader process. This prevents Python's already-loaded math
library from concealing a missing dependency. These are build-recipe and file
proofs plus a native boundary check; they do not prove GCC, linking, runtime
floating-point settings, the actual FMI adapter/model-description XML or the
complete FMU ZIP. The required full gate passed in `build/fmi-build-full-gate.log`.
[CI for f1ce838](https://github.com/CogniPilot/rumoca_lean/actions/runs/34502115582)
also passed.

The SR02 linkage increment generalizes the existing complete numerical
`ArtifactContract` over external or `static inline` declaration tokens, without
changing its source, execution, behavior or rounding obligations. The FMI
profile selects internal linkage and a single compiled adapter translation
unit. `modelIdentifier` is `Rumoca_` followed by the parsed model name. Source
lexical proofs establish a valid C identifier and XML text; distinct model
names have distinct identifiers. Repeated instances share an identifier, and
unrelated artifacts with the same name are not guaranteed distinct namespaces.

`FMI3.SourceBuildContract` also requires decoded modelName/ME/CS identifiers in
the actual model-description XML and the exact source prefix/include fragment
in the actual adapter. The remainder of that adapter is unconstrained by this
fragment proposition. It does not prove full preprocessing, linking, metadata
semantics or whole-adapter behavior. The native binary build uses the official
header's `FMI3_OVERRIDE_FUNCTION_PREFIX`; ordinary source composition retains
the declared prefix. The fixed reader quotes the full adapter as bounded
character blocks and uses `String.ofList` in the proposition; this avoids
kernel reduction of a large UTF-8 builder. `sourcePrefix_of_chars` derives the
same string decomposition from that input's checked character prefix. As with
literal quotation, file reading and faithful input encoding remain part of the
small trusted adapter. The certificate passes in `build/fmi-prefix-certificate.log`.
Thirteen new roots and the generalized existing roots pass
`build/fmi-linkage-package.log`. The targeted artifact/importer/source-link gate
passes in `build/fmi-linkage-artifact-gate.log`, retaining thirteen native test
groups and adding one prefix mutation. Both source FMUs compile from their own
XML recipes, link together and expose only their declared FMI APIs. Failed
native builds preserve earlier FMUs. The required full local gate passed in
`build/fmi-linkage-full-gate.log` at `efb5c80`;
[CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34509004071) also passed.

`Solve.FMI3Model` carries the original Solve model, source names and a prepared
scalar tensor IVP. Its numerical policy remains unit Euler; default start is
zero and the unit source contract permits a finite host override. Both FMI
interfaces use the same local state and constant derivative. A CS instance
contains the ME model data and calls the existing numerical kernel directly;
it never calls ME-only FMI functions on a CS handle. Positive integer
communication steps run that many internal unit steps, with a limit of one
million per call. Unsupported/nonprogressing steps return Discard without
advancing; invalid arguments and calls return Error and enter Terminated.
Final values remain readable there; reset is required before restarting
simulation in this profile.

`Rumoca.FMI3.allowed_correct` in `RumocaCore.FMI3.Lifecycle` checks the mode table against
separately written reference predicates. `Rumoca.FMI3.guard_reference` in `RumocaFMI3.GuardProofs`
proves the constructed C integer/Boolean guard AST accepts exactly those
predicates for every command, interface kind and mode. The reference covers
the selected event-free profile, not the entire FMI standard. It must still
be reviewed against the prose and tables. These theorems **do not** establish
the function-body, memory, printer, callback, Float64 time or lifetime bridge.
`metadata_name` and the prepared-Solve projections are limited metadata facts,
not an XML schema or complete correlated-metadata theorem.

`RumocaC.Memory`, `Body` and `RumocaFMI3.StateProofs` add an object-level memory
and small-step body contract. Cells have declared types, writable permissions
and optional initialized contents. Loads reject missing, uninitialized or
ill-typed contents; stores require a writable existing cell and a supported
type conversion. Float64 contents are actual `BitVec 64` payloads, with finite
values connected to the existing binary64 encoding bijection. Addresses use
block identity, struct-member paths and array offsets; byte layout and the
native pointer ABI are not formalized by this representation.

`RumocaFMI3.LifecycleGuard.reference` connects the generated guard to those
same reference predicates in `CBody.eval`, using the actual symbolic heap.
`require_run` executes the complete three-step instance/lifecycle prefix for
every existing command, interface kind and represented mode. It preserves the
entire heap and selects either the remaining body or the emitted failure call.
The premises supply the instance binding, a fresh local `m`, and readable
kind/mode fields. `reject_prefix` stops at the failure helper; it does not
claim that logging or the final Error return has been executed.

`LifecycleBodies.terminate_correct` proves every behavior of the successful
ME/CS termination body: OK status, Terminated mode, and model/history
preservation. Its general mode-write frame protects all other cells.
`failure_mode_run` executes the actual error helper's first write and reaches
its logger; it is not a complete failed-call theorem. The state and derivative
getter proofs now cover Terminated through the common guard theorem, matching
the final-query requirement in FMI 3.0.2 §2.3.8. Core/C/FMI checks passed in
`build/fmi-termination-package.log`. The actual combined FMU, independent ME/CS
importers, native ABI and runner passed in `build/fmi-termination-artifact.log`.
The complete cross-package gate remains required. No additional source grammar
or solver is admitted by this correction.

The event/completed-step prefix and both successful initialization bodies now
use this shared guard theorem. `CBody.run_add` composes blocks through their
exact intermediate machine state. Their existing all-behavior, frame and
history/model theorems retain their statements. The shared C and FMI audits
passed in `build/fmi-lifecycle-guard-package.log`; no runtime or grammar case
changed, and these package checks do not replace the actual-artifact gate.

`StateProofs.get_behaviors` proves every behavior of the actual generated
`fmi3GetContinuousStates` body returns OK and copies the model's exact finite
encoding to the caller buffer in each permitted ME mode. `set_behaviors`
proves the corresponding `fmi3SetContinuousStates` body implements the shared
ME state update in Continuous-Time Mode. Their observations include the full
final heap. Frame theorems preserve every other address and other instance
blocks. The caller must provide correctly typed, accessible storage; separate
blocks justify ownership claims. `null_instance_behaviors` proves the common
prefix returns Error without changing memory when given a null handle.

These proofs evaluate the existing generated statement trees with independent
rules for declarations, branches, loads, stores and returns. They do not
replace FMI calls by their intended results. The pure `isfinite` intrinsic
uses the encoding's finite-range predicate.

`RumocaC.Calls` extends the memory machine with fresh parameter scopes,
checked arity and conversions, call frames and converted returns. Successful
memory transitions lift unchanged (`body_step`, `body_reaches`), and
`body_behaviors` lifts the existing terminating body contracts when the
declared return conversion succeeds. This is a successful-execution extension,
not equivalence for old stuck states: ordinary calls can now execute.
The linked program selects the actual `Runtime.helpers` trees and the existing
`CStatements` numerical program. Every numerical statement executes with the
caller heap carried unchanged; `kernel_correct` proves that bridge. Dispatch
never supplies a numerical result merely because of a function's name.

`CallProofs.model_rhs_reaches` follows the model helper into the numerical RHS.
`model_advance_behaviors` covers every finite state and uint64 count: the helper
loads state, calls the numerical sampler, writes its exact encoding and returns
void. Its final heap agrees with shared `CoSimulation.run` model state; other
addresses are unchanged by the existing frame theorem. This proves the internal
helper, not the public `fmi3DoStep` time, status and admissibility logic.
`DerivativeProofs.get_behaviors` covers the actual generated ME derivative getter
in initialization, event and continuous modes. It follows both helper calls and
returns OK with the shared ME derivative in a valid writable output cell.
Its all-behavior conclusion excludes divergence and stuck execution and includes
the full final heap. As with state access, entry bindings and accessible typed
storage are explicit premises; this is not a byte-layout or public ABI theorem.

`RumocaCore.Real.Comparison` classifies actual binary64 encodings as finite,
positive/negative infinity or NaN. Finite comparisons reuse the encoding
bijection and exact integer units. `test_finite` proves all six comparison
results agree with mathematical real order; signed zeros compare equal.
`decode_nan` and the unordered theorems cover every NaN payload. The C-tree
interpreter uses these comparisons, including its existing supported conversions
of integer zero and one. General integer-to-double conversion remains unsupported.
Comparison results do not model floating exception flags or signaling traps.
This distinction matters under the C floating environment; see
[C11 draft N1570 §§7.12.14 and F.9.3](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).

`RumocaCore.FMI3.Time.Window` independently states the ME time-history lower
bounds from [FMI 3.0.2 §3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3SetTime):
start time, the second-last completed step and last event-mode entry. The
runtime's optional experiment stop adds an upper bound. `TimeProofs.guard_reference`
proves the actual generated validation expression accepts exactly this window
for finite inputs, assuming `timeMin` represents the maximum of those history
bounds and the stop fields represent the optional stop. `guard_nonfinite`
proves rejection before either bound is read. `set_behaviors` proves every
successful generated `fmi3SetTime` body returns OK, stores the exact input
encoding and preserves all other cells, including the shared ME model state.
The existing call-machine lifting supplies the all-behavior result.

`RumocaCore.FMI3.History` relates a positional reference history to the compact
runtime clock. Its invariant retains the experiment/event floor separately
from completion history; no monotonic-completion premise is introduced.
`trace_represents` proves preservation over every admitted reference sequence
of time updates, completions and event entries. The generated runtime now
stores `eventTime`, initialized with `startTime`, and recomputes `timeMin`
from that event floor and the previous `lastCompleted` at each completion.
This drops obsolete completion bounds. The old running maximum over-rejected
`SetTime(1.5)` after completions at `1, 2, 1, 2` even though each time query
satisfies the reference interval. Event entry preserves both the event floor
and the still-applicable second-last-completion bound.

`HistoryProofs.initial_correct`, `event_correct` and `completed_correct`
execute the actual generated history blocks under the independent C-tree
small-step rules, prove their final heaps represent the corresponding
reference updates, and preserve an arbitrary code continuation. Separate
frame theorems preserve every cell outside each block's writes. The field
comparison and conditional store are proved for all finite encodings, with
typed writable storage as a premise. `stored_guard_reference` connects the
maintained clock representation to the existing SetTime guard theorem.

`HistoryBodies.event_correct` and `completed_correct` now compose the complete
successful public `fmi3EnterEventMode` and `fmi3CompletedIntegratorStep` bodies
with the reference history, reference lifecycle mode and shared Solve/ME state.
The execution includes the instance and lifecycle guards, output-pointer guards,
both Boolean output writes, the history blocks, the event-mode write and OK
return as applicable. Every behavior terminates with the specified full heap;
divergence and stuck behavior are excluded under the stated entry conditions.
The call-machine lifting also accepts compositional reachability proofs through
`body_behaviors_of_reaches`, without changing the interpreter.

The instance clock fields must be finite, typed and writable; the event-mode
cell must be writable for event entry. Completion outputs require writable
Boolean cells and may be uninitialized or alias each other. Their storage
blocks are separate from the instance. The frame theorems preserve every cell
outside the actual write addresses; preserving another instance also requires
its storage to be separate from caller output writes. The model-state
corollaries preserve its exact Float64 encoding. These are symbolic-memory
body contracts with supplied parameter bindings, not byte-layout or public ABI
entry theorems.

Kernel mutation controls distinguish a missing event-mode write and a changed
output value from the correct successful bodies. They also check uninitialized,
missing and read-only output storage. Native tests cover aliased/distinct
outputs, both values of the unused FMU-state flag, signed-zero model state and
instance isolation.

`InitializationBodies.exit_correct` covers every behavior of the complete
successful `fmi3ExitInitializationMode` body for both ME and CS. It proves
termination with OK, agreement with the reference lifecycle transition, and
preservation of the shared model state and clock history. `exit_frame`
preserves every cell except the instance mode. The premises supply the
instance parameter, its interface kind, and a typed writable mode cell in
Initialization Mode. The existing event-free profile moves ME to Event Mode
and CS to Step Mode. This is a symbolic-memory body theorem; ABI entry,
rejected calls and printed-adapter binding remain separate obligations.
All seven new roots passed the unchanged axiom audit with
`lake build check-fmi3` in `build/fmi-initialization-exit-package.log`.
The aggregate `lake build audit` also passed in
`build/fmi-initialization-exit-audit.log`. No emitter or grammar changed in
this proof increment; these checks do not replace the required artifact gate.

`RumocaCore.FMI3.Initialization` now states the corrected unit admission profile
independently of C: start is finite and an enabled stop is finite and no earlier
than start. The unused tolerance and undefined stop retain arbitrary bits,
including NaNs. `atLeast_iff` connects its executable bit comparison to inclusive
Real order through the finite encoding bijection. The earlier finite-start body
proofs remain checked under this policy; the complete raw-argument classification
also covers nonfinite starts and rejection before any clock/state write.

`InitializationEntry.correct` covers every behavior of the complete successful
`fmi3EnterInitializationMode` body for both ME and CS. It executes the instance,
lifecycle and argument guards, four clock writes, stop/flag writes, mode change
and OK return. The final heap preserves the shared model state, represents the
initial reference history, and discharges the representation premises of the
existing `SetTime` guard theorem, including its optional stop. A full-heap frame
preserves all cells outside these seven writes. Stop and flag storage may be
uninitialized; the pre-existing clock cells must represent a finite writable
clock. Supplied entry bindings, a valid kind and a writable Instantiated mode
cell remain premises. This does not yet prove allocation establishes them.
The package audit passed in `build/fmi-initialization-entry-package.log`.
`then_exit` composes the complete entry and exit body contracts through the
same intermediate heap, retaining model state, initialized history and the
reference final mode. The aggregate audit, including this composition, passed
in `build/fmi-initialization-entry-audit.log`. This proof-only increment changes
no emitted code or grammar; its audits supplement the passing publication gate.

Those earlier body-only checkpoints used the strict policy at their recorded
revisions. The new `InitializationCalls`/`InitializationExit` contracts cover
ordinary typed public entry and return, null calls, lifecycle and raw-argument
failures, disabled logging and all represented returning logger outcomes. The
mandatory actual-file contract includes both printed fragments and their exact
function table. `QuietExecutionContract.initialize` composes entry/exit through
one intermediate heap without assuming a finite old clock; its source contract
derives the unique IVP from actual finite state storage. The corresponding
required artifact gate passed in `build/c-initialization/full-gate.log`.
General host/lifecycle histories, instance storage,
lifetime, complete CS execution and native ABI correspondence remain open.

The SR04 correction removes nominal-state queries from Instantiated after
independent review of FMI 3.0.2 §2.3.2. `ErrorBodies.nominals_reject_run` proves
the actual generated query reaches its failure call with the whole heap intact;
it requires no output-pointer premise because rejection precedes output access.
`nominals_reject_reaches` embeds this prefix in the typed tensor-call machine.
`failure_dispatch_run` covers both logging settings and `failure_log_arguments`
identifies the actual callback arguments. `failure_silent_correct` proves all
typed body-entry behaviors return Error and change only the mode cell when
logging is disabled. Enabled callback execution, string parameter binding and
the actual printed query/helper are outside those statements. This does not
yet close the failed-call or entire-FMU contract.

`RumocaC.BodyEmbedding` proves that successful `CBody` evaluation, steps and
finite runs are preserved by `CLoops`, carrying the same code, values and heap
with local type bindings. It then derives ordinary typed returns and all-body
behavior equivalence. `RumocaFMI3.BodyEmbedding` applies that bridge to the
generated runtime bodies and reuses the complete termination proof. The initial
scope premise excluded SetFloat64: its empty-array branch declared a local
variable, which the typed model rejects without block-scope semantics.
This limitation was found by attempting the universal scope proof, rather than
assuming every existing body embeds. It is not a defect in C's block semantics.
Sixteen added roots pass `build/fmi-error-embedding-audit.log`. The lifecycle
check rejects the old FMU, and the corrected artifact passes all thirteen native
groups plus the actual-file/source-link/mutation gate in
`build/fmi-nominals-artifact-gate.log`. The required full gate passed in
`build/fmi-nominals-full-gate.log` and in
[CI for 904e9bd](https://github.com/CogniPilot/rumoca_lean/actions/runs/34512618273).
Production language acceptance is unchanged.

The subsequent setter refactor hoists the instance declaration and shares the
mode guard, preserving all checks and the existing value-validation/write
suffix. `SetterScope.nonnull_equivalent` and `null_equivalent` preserve every
`CCalls` behavior for arbitrary suffixes, programs and caller continuations.
They use a general finite-prefix equivalence theorem in `Transition.Prefix`;
no successful termination assumption hides wrong or divergent outcomes.
`emitted` binds the actual setter to that form. `empty_behaviors` and
`null_behaviors` prove complete typed body-entry termination with unchanged
heap, and `entry_reaches` covers the nonempty lifecycle prefix before its value
operations or failure call. `BodyEmbedding.body_closed` now quantifies over
all generated FMI bodies, with no setter exclusion and the unchanged nested
declaration restriction. Nine new roots pass `build/fmi-setter-scope-audit.log`;
all thirteen existing native groups and the actual-file/source-link/mutation
gate pass in `build/fmi-setter-scope-artifact-gate.log`. The required full gate
passed in `build/fmi-setter-scope-full-gate.log` at `1a53884`, and
[its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34516914151)
passed. That full run's FMU has SHA-256
`765662ef91d429089b4a22fd12dd29ec885f375a39a173c02bd4c8c35343a56f`.

The next increment adds the unsized-array parameter adjustment from
[C11 N1570 §6.7.6.3 paragraph 7](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
`CCalls.parameterType` preserves the declared pointee spelling, including
`const`, and requires the adjusted pointer type to resolve in the explicit
header dictionary. Binding still rejects unknown types, duplicate names,
wrong arity and unsupported conversions. `CallParameters.parameters_typed`
derives the matching local type environment and conversion-stable values from
successful binding; `parameters_length` and `parameters_unknown` prove the
arity and unknown-type obligations. `BodyEmbedding.typed_call_reaches` and
`typed_call_behaviors` lift a checked body run through ordinary function entry
and return, without assuming prebound locals or an arbitrary type environment.

`StateCalls.get_behaviors` and `set_behaviors` apply that bridge to complete ME
continuous-state calls. They execute the same function constructor used by
`Runtime.render`, preserving exact binary64 values and the whole-heap frame
of the existing Solve ME observation/update proofs. Only the required Float64
pointer spellings were added to the FMI type dictionary. These calls require
the explicit function-table binding, valid caller/instance storage and the
stated lifecycle preconditions. Official-header parsing, actual adapter text,
native ABI/linkage, other public signatures and rejected-call execution remain
separate obligations. All twelve added roots and the full package audit pass
in `build/fmi-array-call-audit.log`, with the unchanged axiom whitelist. The
FMI actual-file/source-build/mutation gate and all thirteen existing native
groups also pass in `build/fmi-array-call-full-gate.log`. That required full
local run passed at `30ef448`, including the complete GALEC/eFMU archive,
extracted-manifest and mutation checks;
[its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34521375057)
also passed. Its FMU has SHA-256
`782bc82fa92e2149c531d0ee53e1f9eb7a4760f6b54223f28093c541130d7ae2`.
No new Modelica source case is admitted.

Ordinary calls are supported as entire assignment, declaration, return or
discard operands; their arguments are pure expressions. The typed tensor-call
machine additionally supports declared-local writes and its selected arithmetic
operators; the original memory-body machine does not. Function pointers,
remaining parameter forms and typedefs, nested effectful expressions, block scopes,
allocation/free, callbacks, general C arithmetic and remaining FMI bodies need
additional rules and proofs. The selected generated assignments call pure
numerical functions or the read-only RHS helper, so evaluating their lvalues
after the call cannot observe a callee memory change. General C evaluation-order
correspondence remains part of the target review. Unsupported operations are
stuck. The successful-body results do not prove the non-null logging/error
paths, connect body trees to the actual printed adapter bytes, or extend
`ArtifactContract` to the whole FMU.

The additional kernel-checked negative controls distinguish a constant-valued
copy from the correct state copy, expose aliasing into another instance,
and reject missing storage and unsupported calls in the base memory machine.
Call regressions additionally detect a changed helper return and an unbound
numerical RHS; reject bad arity, duplicate parameters and unknown symbols;
and reject nonfinite numerical input and an out-of-range counter. Time controls
cover signed zeros, adjacent/subnormal values, infinities, quiet/signaling NaN
encodings, valid backtracking, absent stop storage, both interval boundaries
and a mutated time write. These are authored-model regressions, alongside
independent native ABI tests for the same time and state boundaries.

The required gate now also validates the actual ZIP/XML with FMPy and runs
ME/CS simulations, raw ABI lifecycle/error/time/binary64 regressions and an
independent C source rebuild. Runner CSVs and nonzero failure propagation are
checked. FMPy, its ME Euler solver, the native ABI adapter and packaging are
outside the whole-compiler theorem. The included kernel audit log records a
check performed during creation; it is not a standalone proof or signature
authenticating all members of an arbitrary archive. Full actual-FMU binding
and the public FMI conformance capstone remain open.

## Tiny eFMI Algorithm Code

`rumoca MODEL.mo -o MODEL.alg` emits the checked unit integrator's GALEC block.
It selects zero initialization and a fixed one-second period within the
existing host-initialized source profile. This does not add Modelica syntax.
Names in the emitted block are canonical; the checked product retains its
original source-indexed DAE. The authority and Beta 1 draft discrepancies are
recorded in [the eFMI review](../dev/efmi.md).

`GALEC.lower_equation_correct` checks admission of the unit DAE.
`GALEC.lower_step_correct` compares the projected method with the existing
finite numerical profile. The executable Algorithm Code refinement itself
comes from `Solve.Algorithm.lower`, without reconstructing DAE or repeating
the numerical IVP lowering. Its register references retain tensor shapes;
`lowerExpr_correct` preserves the expression interpretation for every shape
and arithmetic operation. `UnitProfile.lower_correct` additionally includes
the explicit clock-initialization program, not a backend-chosen literal.

`GALEC.Protocol.lower_trace_correct` transports every trace of the restricted
lifecycle reference. Entering and completing a method are separate events;
only idle permits output reads or another method entry. A sampling tick enters
DoStep once, and shutdown is terminal. This proves the connection between two
formal block interpreters under the authored protocol. It does not verify
concurrent host scheduling, C instance memory or an ABI implementation.

The independent GALEC scanner, named action checks and shared LR engine bind
emitted characters to the admitted block. A checked profile-specific input
bound covers the fixed token skeleton with arbitrary lexically admitted names.
`GALEC.Generated.grammar_processed` checks processing of the actual embedded
EBNF into its CFG. These facts do not establish general LR table completeness
or conformance of the EBNF reader to ISO 14977.

`EFMI.AlgorithmContract` combines source lexing/grammar membership, concrete
GALEC grammar processing, parsing/denotation of the actual `.alg` bytes, DAE
admission, binary64 methods/samples and full state/lifecycle refinement to
Solve. `EFMIArtifactCheck` independently reads the Modelica input, both EBNFs
and the actual `.alg` file. Its fixed proposition includes the two grammar
equalities and successful compilation with this contract. It audits that
theorem's dependencies before publication; producer-supplied proofs are not
executed. File I/O, the file-to-proposition adapter and atomic publication have
the same trusted-infrastructure status as the existing C artifact checker.

Use `rumoca verify-algorithm MODEL.alg --source MODEL.mo` for a standalone
member, or `rumoca verify-efmi INPUT --source MODEL.mo` for the prepared tiny
directory or complete `.efmu` archive. The CLI uses the pinned `lean4-cli` dependency and passes explicit
process arguments to fixed checking entry points. It does not generate Lean
commands from user text. The original source remains an explicit input; the
workspace determines the default grammar files. No eFMI input environment
variables are needed. The adapters share one read of each code/source file
when composing their theorems.

The directory adapter fixes the current emitted layout: `__content.xml`,
`AlgorithmCode/{manifest.xml,model.alg}` and
`ProductionCode/{manifest.xml,production.c}`. A restricted root-header reader
extracts candidate IDs and the generation time from the actual manifests.
It does not authorize XML acceptance: the manifest certificate still requires
the complete actual strings to equal the prepared trees and checks the
independent XML output grammar. The reader proposes identity strings; a separate
kernel decision proves their required identity profile. It is not a general
XML parser. Directory checking covers the five code/XML files. Archive checking
additionally binds the complete ZIP structure and all pinned resources; neither
path imports arbitrary eFMI representation layouts.

The full gate audits these roots and checks grammar/namespace reuse, source
acceptance/rejection, and mutations of arithmetic, clock initialization and
both actual grammars. The manifest checker composes the XML/reference/checksum
correlation with that same code contract. The `.efmu` output path uses the pure
`Artifact.efmuArchive` generator, checks the staged source and complete archive,
audits the fixed theorem, and then renames the checked file into place. A checked
`.alg` member alone does not supply this archive contract.

Candidate identities come from `IO.getRandomBytes` with the UUIDv4 layout
described in [RFC 9562 §5.4](https://www.rfc-editor.org/rfc/rfc9562.html#section-5.4).
The timestamp comes from `Std.Time.Timestamp.now`, formatted in UTC. The existing
manifest and actual-file contracts check whole-string identity validity, calendar
validity and distinctness within this archive. They do not assume the producer's
native decisions are proofs, nor establish entropy quality, global uniqueness
or clock accuracy. No identity work is added to DAE or Solve IR. Staging in the
destination directory permits a same-filesystem rename; file I/O, process
execution and publication remain tested infrastructure.

## Tiny eFMI Production C

The [standards review](../dev/standards-review.md) found that the previous
status-zero proof did not connect the C result to the manifest's error anchor.
The correction now declares an `EfmiStatus errorSignalStatus` instance field.
Every unit method clears it on entry and returns its stored value. Startup
accepts allocated, writable but uninitialized state, clock and status cells;
later methods require finite state/clock cells and writable status storage.
The previous status bits are arbitrary. Complete method execution still
preserves the exact numerical Solve result and every cell outside the three
declared instance fields; other instances are unchanged.

`Manifest.MappedStatus` requires a unique decoded mapping from the actual
Algorithm Code error anchor and C formal parameter to a declared status field.
`mapped_status` and `mapped_startup_status` connect that field to the actual
returned value, including uninitialized Startup storage. Both are conjuncts
of `ManifestContract`; `ManifestContract.status_observations` exposes their
composition with the actual XML/C members. `ArchiveContract` therefore also
requires them. The certified C printer's independent tokens include the
status store and return; the header contract describes all three fields.
Nine new roots pass the unchanged axiom audit in `build/efmi-status-package.log`.
The required complete artifact gate passed in `build/efmi-status-full-gate.log`,
including the actual archive theorem and redirected-status rejection.
[CI for feb57a9](https://github.com/CogniPilot/rumoca_lean/actions/runs/34499145712)
also passed.
The unit profile still has no exposed error signals. This correction neither
adds general GALEC error handling nor establishes full eFMI standards compliance.

`Solve.Algorithm.Model` retains the GALEC product and the proof that its block
is the actual algorithm lowering. `Production.lower` reads only that block.
It emits a fresh C local for each fill/add instruction and stores the return
register in the appropriate instance field. Startup explicitly executes the
clock program as well as the state program. Unsupported non-scalar storage
is rejected without enumerating tensor coordinates.

The three generated functions use a caller-owned `Model *` with separate
binary64 `x` and `samplePeriod` subobjects. `Production.method_correct` checks
every behavior of each method: it returns status zero with the exact Solve result,
preserves the clock except during Startup, and preserves unrelated memory.
Startup also has a separate theorem for allocated but uninitialized storage.
Typed parameter binding, initialized finite storage for subsequent calls, and
serialized host use are explicit preconditions. The tiny API does not contain
runtime checks for invalid pointers or host lifecycle misuse.

The interface declares `EfmiReal` as `double` and `EfmiStatus` as `int32_t`.
The structure fields use `EfmiReal`; all entry points return `EfmiStatus`.
`CHeader.header_declares` checks the header against an independent fixed token
grammar for these typedefs and fields. `Production.return_checked` checks the
returned zero against the actual declared return type. This avoids the Beta 1
prose/schema disagreement about return metadata for void functions. The status
reports successful completion under the existing preconditions; no additional
GALEC error modes or source cases have been introduced.

`CProtocol.trace_sound` and `trace_complete` connect legal serial interactions
of these actual C bodies to the Solve protocol, including output state and the
number of completed sampling calls. Method execution uses the target machine,
not a function-name lookup returning the intended value. These traces compose
with the existing GALEC/Solve theorem; they do not prove physical scheduling.

`EFMI.CSyntax.Denotes` specifies declarations, pointer-member accesses, finite
constants, additions, assignments and function headers using an independent
maximal-munch token grammar. `EFMI.CSyntax.program_render` proves that every
valid program in this syntax profile renders with the same execution-tree
denotation. Its component proofs quantify over names, expressions, statement
lists, indentation and lexical continuations. The compiler contract composes
this structural printer theorem with method execution and protocol preservation;
there is no executable Production C reader. The fixed preamble is checked as a
prefix, including the storage declaration and binary64 preprocessor guards.
Its correspondence to object layout and preprocessing remains reviewed
infrastructure. The separate fixed-header certificate still uses the shared scanner soundness
theorem. These printer theorems cover the tiny numerical and straight-line
eFMI function profiles, not the entire FMI 3 adapter or arbitrary ISO C.

The required full gate passed after the printer migration with exit status zero
in `build/c-printer-full-gate.log`. The actual source/C and combined eFMI
contract audits are preserved in `build/c-printer-artifact-contract.log` and
`build/c-printer-efmi-artifact-contract.log`. No new axiom or source-language
case was introduced.

The shared `CTree` string-expression printer now also has an independent
literal contract in `RumocaC.StringLiteral`. `CString.render_correct` proves
for every Lean string that the printed C literal uniquely denotes its UTF-8
payload followed by zero, including empty strings and embedded zero bytes.
It also proves that the modeled trigraph and line-splice rewrites cannot
change the emitted characters. The actual emitter escapes question marks;
three-digit octal escapes prevent following digits from changing a byte.
The selected rules follow [C11 N1570 §§5.1.1.2, 5.2.1.1, 6.4.4.4 and 6.4.5](https://www9.open-std.org/JTC1/SC22/WG14/www/docs/n1570.pdf)
under an explicit eight-bit ASCII source/execution profile.

Four new public roots pass the unchanged axiom audit in
`build/c-string-printer-audit.log`. A disposable native boundary reproduction
uses the actual expression printer on the formerly corrupted `??/n` payload
and passes strict C11 compilation and byte observation in
`build/c-string-trigraph-after.log`. The required full local gate passed at
`a0327a1` in `build/c-string-printer-full-gate.log`, including both artifact
paths; [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34527453846)
also passed. The decoder in the proof module is not a compiler pass.
The proposition describes literal object bytes, not allocation,
static lifetime, pointer decay, header binding, logger execution or surrounding
adapter syntax. Those obligations and the full FMI artifact contract remain
open; this repair admits no new grammar case.

The next storage increment uses Std's `UInt8`/`Int8` conversions in
`CCharacter`. It proves byte/value round trips for unsigned or two's-complement
signed eight-bit characters; the inverse for integer inputs requires a
representable value. `CMemory.convert` accepts only representable character
values. This is a partial conversion profile, not a claim about arbitrary C
casts or every implementation-defined signed representation.

`CReadOnly.typed_reaches` proves that all existing read-only cells survive
every reachable prefix of the authored typed-call machine, including its
ordinary returns. The analogous body/loop invariants and a load-preservation
corollary are also proved. `CLiteral.installed` constructs symbolic storage
for every UTF-8 payload and terminating zero; fresh-block installation preserves
previously supplied objects. `CLiteral.rendered_memory` binds decoded bytes of
the actual expression printer to loads from these typed character objects,
and `Stored.after_steps` preserves that storage through modeled calls.

Nine new audit roots pass in `build/c-literal-storage-audit.log` under the
unchanged axiom policy. The required full gate passed in
`build/c-literal-storage-full-gate.log`, including both target artifacts and
their existing boundary checks. There is no new unit-test suite.
The construction establishes a possible symbolic initial heap, not native
allocation, static lifetime or a global literal-address environment. It does
not require separate addresses for distinct literal texts; C permits literal
storage sharing. That checkpoint retained abstract string expression values;
the next increment below connects their evaluation to pointers. Neither
checkpoint admits a new source case.

`CInterface` now supplies an explicit static literal-address map. `CBody.eval`
decays a supported literal expression to its supplied first-element pointer;
a missing binding rejects evaluation. The abstract `CMemory.Value.string`
constructor is removed. `CLiteral.rendered_pointer` connects the actual
printer's bytes, evaluated pointer and typed character loads under the supplied
storage contract, and `Valid.after_steps` preserves that contract through
modeled calls. The selected map uses one address per literal text and allows
compatible storage sharing; it does not model every native compiler's
per-occurrence allocation. Resolving that representation against actual
adapter globals and native storage remains an explicit obligation.

FMI body proofs now quantify over supplied literal maps while retaining the
same concrete header constants/types. The dictionary additionally resolves
`const char *` and the pinned `fmi3String` pointer alias. `ErrorCalls` proves
ordinary entry and return for the actual failure helper and supplies a shared
theorem for every emitted `return fail(m, message)` statement with logging
disabled. `nominal_reject_correct` composes actual public parameter binding,
the Instantiated guard, literal evaluation, helper execution and return. Every
behavior returns Error and changes only the instance mode to Terminated;
supplied immutable literal storage survives. It covers either interface kind,
all UInt64 counts and arbitrary output pointers, including null, without an
output-dereference premise. An output address that aliases the mode cell is
subject to the stated mode-cell exception in the frame.

All twelve added roots and the existing C/FMI/eFMI/compiler package audits
passed during isolated preparation in `build/c-literal-call-package-audit.log`.
The required full root gate passed in `build/c-literal-call-full-gate.log`,
including both FMI interfaces and the actual eFMU archive/mutation gate.
The [standards review](../dev/standards-review.md#c-literal-pointer-and-rejected-call-increment-standards-impact)
records this run's retained artifact hashes and unchanged grammar identities.
These are function-tree and storage proofs with explicit signature/definition
and literal-binding premises. Complete adapter bytes, static object setup and
lifetime, enabled external callbacks and whole FMI conformance remain open.
No native compiler/ABI proof or new unit-test suite is introduced.

`CLiteral.Lowering` prepares explicit named string storage without changing the
production renderer. Its transformation replaces registered string expressions
with data identifiers and retains unregistered literals. `expression_correct`
preserves value/lvalue evaluation, including failure, and `arguments_correct`
preserves evaluated argument lists. Both sides use the same supplied C interface;
the named identifiers must resolve to the literal pointers and must not collide
with the recognized `isfinite` intrinsic.

`body_behaviors` preserves and reflects every observation of the memory-body
machine: exact returned values and heaps, stuck execution, and divergence.
Freshness of declarations prevents local capture, and the proof preserves that
invariant through branches and loops. It uses the reusable
`Transition.FunctionalBisimulation.behaviors` theorem, whose step reflection and
final-state correspondence do not assume successful termination.
At that checkpoint the theorem covered the memory-body machine. Constructing the
global dictionary, proving freshness against existing identifiers and headers,
printing/initializing static arrays, and binding those declarations to the actual
adapter are still required before the production renderer can use this pass.
The seven new audit roots and core/C package checks pass in
`build/c-literal-lowering-package-audit.log`. The required complete root gate
passed in `build/c-literal-lowering-full-gate.log`; the recurring standards
review records both retained artifact hashes. No new tests or production
language cases were added.

`LiteralLoopLowering` and `LiteralCallLowering` now extend that transformation
to the typed loop and ordinary-call machines. `loop_behaviors` preserves and
reflects their exact returned values/heaps, stuck execution and divergence.
`call_behaviors` composes parameter conversion, fresh callee scopes, loop/body
steps, continuation frames and ordinary returns for arbitrary programs,
including recursive calls. `invocation_behaviors` specializes this result to
public entry with an empty continuation; it does not assume termination.

The proofs require a supplied global dictionary, names fresh against local
parameters/declarations/writes, and structural exclusion of string literals
as direct callees. Both machines still use the same interface. This does not
prove that adding named globals preserves every existing source lookup, nor
construct or print those globals. External callbacks, native storage/ABI and
the complete emitted adapter remain outside this increment. The thirteen new
roots pass the unchanged axiom audit in `build/c-literal-loop-call-package-audit.log`.
The required full gate passed in `build/c-literal-loop-call-full-gate.log`,
including both target artifacts and their existing boundary checks. The
recurring standards review records the exact artifact hashes. No production
renderer, grammar case or test suite is added; the stage remains open.

`LiteralInterface` and `LiteralInterfaceCalls` now prove that extending a
global dictionary preserves all typed-call observations when the original
program's identifier lookups are unchanged. `LiteralPool` constructs checked
named-object candidates with distinct names, texts and block slots. Validation
checks ASCII C identifiers, reserved-name exclusion and a 63-character name
bound. `make_coverage` proves that a successful construction binds exactly the
requested texts, including duplicate requests; name collisions can reject
construction. This is partial correctness, not an unchecked name-generation
totality claim.

`LiteralPoolStorage.storage_valid` derives the literal-byte storage contract
from a concrete symbolic heap construction. Fresh pool blocks preserve every
existing cell, and `storage_after_steps` retains the literal bytes after every
typed-call execution prefix. `LiteralPoolLowering` collects identifiers read,
declared and written by the original code, including function and parameter
names. Its `Pool.invocation_behaviors` composes interface extension and literal
lowering, preserving exact return/heap, failure and divergence observations
between the original and named interfaces. The collected names establish local
freshness and lookup agreement; checked entries establish global bindings.

Header name exclusion, the connection between the function list and definition
table, and structural exclusion of direct string callees remain explicit.
Both interfaces use the constructed pool's literal addresses; no equivalence
to an arbitrary earlier literal-address assignment is claimed. This is still
the authored symbolic C machine: native storage/layout, external calls,
declaration printing and actual adapter binding are not established by these
theorems. The production renderer does not yet use the transformation.
The 27 added roots pass the unchanged C package axiom audit in
`build/c-literal-pool-package-audit.log`. The required full local gate passed
in `build/c-literal-pool-full-gate.log`. The recurring
[standards record](../dev/standards-review.md#checked-literal-pool-and-interface-extension-standards-impact)
tracks the required full gate and the unchanged MLS/FMI/eFMI obligations.

`LiteralDeclaration` and `LiteralDeclarationBlock` add independent syntax for
static character-array declarations. The printer theorem characterizes the
complete ordered sequence of names and initializer bytes, including null
terminators, after every modeled trigraph/splice rewrite. The sequence theorem
also checks physical line boundaries; it does not formalize macro expansion.
`renderBlock_storage` connects independently interpreted declarations to named
lookup and every byte of the constructed immutable symbolic arrays.
`LiteralNames` proves that successful `Pool.make` names use the fixed lowercase
prefix and satisfy the checked identifier/63-character conditions. This is
not a claim about arbitrary unchecked candidates or all native header names.

`LiteralCollection` visits every expression/statement constructor and proves
complete removal of registered string nodes. `FMI3.LiteralPreparation` applies
it to the actual renderer's function list. Its definition table uses that same
list and the prepared numerical kernel, with no supplied tree definitions.
It derives the authored constant-dictionary freshness, helper bindings and
structural call conditions. `lowering_behaviors` then preserves and reflects
every authored-machine observation for successful pool construction, any entry,
arguments and heap. Both sides use the same constructed literal addresses.

These 34 roots extend the package audits; the gate record is in
[the standards review](../dev/standards-review.md#literal-declarations-and-fmi-function-binding-standards-impact).
The renderer still emits its existing C. Full translation-unit syntax,
header/ABI correspondence, actual adapter-byte binding, callbacks and native
allocation/layout remain open. In particular, equality of observations in a
machine with unsupported external calls includes their stuck observations;
it is not a proof that every FMI call executes successfully or conforms.

`FMI3.LiteralRejection.nominal_reject` now composes that preparation with the
complete Instantiated nominal-query rejection, for either interface kind,
arbitrary output pointer/count and disabled logging. It derives the message
address, immutable bytes and helper/function bindings from the checked pool
and renderer's table. All call observations return Error, update only the mode
cell and preserve every literal object's bytes. Successful pool construction,
unique function names, inclusion of the nominal signature and fresh storage
remain explicit. `Header.signatures_unique` proves uniqueness for every
successful header-reader result; helper/public name separation and actual
signature membership are still separate obligations.

The shared scanner now selects a matching configured pair before a single
symbol. `Scanner.lex_disjoint` proves exact results and diagnostic preservation
for the previous disjoint configurations; both GALEC and Production C instantiate
it. `CTree.Syntax` proves lexical prefixes for valid names and printed naturals.
`CDecimal.render_denotes` separately proves canonical digits and their base-10
value, excluding leading-zero octal ambiguity. These are printer prerequisites,
not complete C expression syntax, integer type/range or whole-file guarantees.
The [increment's standards and gate record](../dev/standards-review.md#adapter-call-and-lexical-preparation-standards-impact)
keeps those limitations explicit.

`EFMIProductionArtifactCheck` reads the source, both EBNFs, GALEC and C files
and constructs a fixed existential theorem with one compiler artifact and
`ProductionContract` for both members. The kernel and exact-root axiom audit
authorize acceptance. This contract includes source/DAE admission, algorithm
refinement, actual C text denotation, typed entry, full memory effects and both trace
directions. It does not yet cover serialized XML, checksums or ZIP structure.

The contract also recovers the actual GALEC declaration names and includes
`Metadata.Contract` for the same lowered C module. This checks exported method
signatures, real typedefs and structure fields. `Metadata.execution_preserves`
follows the actual C behavior: reading either logical variable through the
described formal parameter and component observes its exact Solve tensor
value, and the return status is zero. Mapping identifiers are proved unique.
These are the typed mapping obligations. `ManifestContract` binds the serialized
XML and foreign-manifest/checksum construction to the same lowered module.

`EFMIManifestArtifactCheck` constructs and audits the exact
`Rumoca.CheckedEFMIFiles.source_to_manifests` theorem from the actual source,
both grammars, GALEC, C and all three XML files. XML rendering is certified by
composing element character lists, checking their equality to a flat list,
and using the standard library's string/list correspondence. Separate header
and child certificates establish the restricted XML output grammar. SHA-1
certificates check UTF-8 encoding, padding and each compression block. Native
candidate generation supplies no proof authority, and no native-reduction
axiom is used.

Manifest names are supplied from `a.parsed.ast.name`. The backend receives
this prepared metadata explicitly and performs no source name resolution.
`Manifest.prepare_named` proves that all three root attribute lists retain
the supplied name. `ManifestContract.source_name` connects these attributes
to the actual XML strings through the independent `XML.Document` relation.
The actual-file checker constructs a kernel-checked `Parsed` witness for the
source and uses parser determinism to bind its quoted name to the artifact's
AST. A native name comparison alone cannot establish the contract. Canonical
GALEC block and C function identifiers remain part of the existing interface
profile; manifest names describe the originating Modelica model.
The full gate passed with these stronger contracts in
`build/efmi-source-name-full-gate.log`; the exact actual-file root audit and
stale-manifest rejection are retained in `build/efmi-source-name-artifact.log`
and `build/efmi-source-name-rejection.log`.

`ManifestContract.identity_valid` requires whole-string membership in the
brace-delimited 8-4-4-4-12 hexadecimal UUID layout, and distinct IDs after case
normalization. It also requires a `YYYY-MM-DDTHH:MM:SSZ` timestamp with a valid
Gregorian date, reusing `Std.Time` for month lengths and leap years.
`Identity.utc_fields` recovers a checked `Std.Time.PlainDate` with exactly the
digits read from that timestamp. The emitted profile admits years 0001–9999,
hours 00–23, and minutes/seconds 00–59. `prepare_identified` binds these facts
to the root attributes of each actual document. This proves the selected
lexical/calendar profile, not global UUID freshness, wall-clock accuracy, or
acceptance of every alternate `xs:dateTime` representation.

The strengthened actual manifest contract passed the kernel and exact-root
audit in `build/efmi-identity-manifest-contract.log`. The complete required
gate passed with exit status zero in `build/efmi-identity-full-gate.log`,
including rejection of an impossible calendar date despite a consistent
checksum graph. Official XSD validation and independent checksum comparisons
are integration checks; they do not license the Lean theorem.
General XSD semantics remain a review obligation; the current SR06 disposition
below records the checker's format limitation. E05/E06 are incomplete.
The later archive and publication checkpoints extend
this manifest contract. See
[the checkpoint and remaining work](../dev/efmi.md).

The production integration gate tests native Startup/Recalibrate/DoStep,
uninitialized storage, independent instances and binary64 boundary cases.
Actual-file negative controls alter a state reference, initialization, store
target, the GALEC member, and append an extra C function. Host tests support
the authored C/IEEE review; native C compilation is not a proved lowering.

The eFMU transport has a separate `StoredZIP.Format` byte
grammar. Its stored ZIP32 profile fixes local and central records, raw member
bytes and CRCs, offsets, lengths and the final directory record. Names must be
unique ASCII relative paths; encryption, compression, extra fields, directory
entries and comments are excluded. `encode_sound` proves that the tail-recursive
ByteArray writer satisfies this list-based specification. `encode_complete`
proves generation succeeds for every admissible member sequence.

`decode_sound` proves that every accepted archive matches the complete byte
grammar. The cursor reader proposes members; an independent final validator
checks the actual complete bytes. This is a soundness theorem, not yet a
completeness theorem for the cursor reader. `number_value` proves numeric
field decoding for every representable value and width. Member inclusion and
whole-byte uniqueness keep this contract tied to the actual archive, without
assuming checksum collision resistance. Review of the authored format against
[PKWARE APPNOTE](https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT)
and of CRC-32 against its specified recurrence remains part of the standards
boundary. The compiler's `ArchiveContract` composes these transport results
with the correlated eFMI XML graph and existing source/C execution contract.
`archive_code_correct`, `efmu_archive_correct` and `compile_archive_verified`
prove correctness of the pure preparation and archive-generation functions.
The combined source-to-archive actual-file gate passed in
`build/efmi-archive-full-gate.log`. The CLI now stages this complete product and
requires that certificate before publication. The new public path passed the
complete required gate in `build/efmi-publication-full-gate.log`, including
independent extraction, schemas/checksums, native C, mutation rejection and
failure-preserving publication. The retained product is `build/Integrator.efmu`;
`build/efmi-publication-artifact.log` audits its four exact roots. The pinned
official checker rejects these same bytes at its extension/layout checks,
as recorded in `build/efmi-publication-official.log`; no official-checker
conformance pass is claimed.
The current [SR06 disposition](../dev/standards-review.md#sr06--resolved-packaging-question-documented-checker-limitation)
classifies those entry guards as a pinned-tool limitation: Beta 1 Chapter 2
permits the emitted standalone layout. The required gate and artifact contract
are unchanged. General standards correspondence, coding guidelines and the
other release obligations remain open.
No full eFMI conformance claim follows from the authored byte grammar alone.

## Binary64 and real refinement

The development tensor profile additionally uses `Real.ScaledRounding`,
`Real.Multiplication` and `Real.Addition`. Product rounding compares exact
integer cross-products on the binary64 grid; it never truncates the product
to an integer before rounding. The nearest/even/canonical relation has a unique
result, and the product relation separately fixes signed zero. `multiply?`
accepts exactly that relation within the strict finite overflow interval.
Its guard is proved equivalent to the Real interval; strict underflow returns
the sign-selected zero. Exactness and half-spacing error bounds are proved.
The scaled rule at denominator one agrees with the original rounding rule.

`Solve.Tensor.Finite` gives an independent execution relation for literals,
addition and multiplication on whole tensors. Execution exists exactly when
every ordered operation is in domain, and its result equals the array evaluator
with the explicit binary64 arithmetic. This includes unused intermediate
instructions: a target may not silently remove their overflow checks. The
actual square program's result is nearest to the Real RHS at every coordinate;
the AD coefficient program's result is nearest to the Real derivative `2*u`.
These are mathematical specifications used in proofs, not an implementation
of native floating-point arithmetic or a derivative of IEEE rounding.
Exception flags, traps, nonfinite inputs and the C/FMI failure policy remain
outside this new numerical contract. The production unit contract below is
unchanged.

`Binary64.Value` contains all finite encodings, including both signed zeros;
NaNs and infinities are outside the input domain. Values decode to signed
integers in units of `2^-1074`, divided by `2^1074` for the real interpretation.
The encoding covers subnormal and normal values with 52 fraction bits and
exponent fields 0 through 2046. `finiteEncodingEquiv` is a proved bijection to
the finite subset of `BitVec 64`; both inverse laws, exponent/fraction decoding
and signed-zero bit patterns are proved in `Real/Encoding.lean`.

`RoundsNearestEven` independently specifies the nearest finite encoding,
even parity on a distance tie, and canonical +0 on the duplicated-zero tie.
`round` is a noncomputable finite minimum with proved existence, specification
and uniqueness. Its kernel-checked opaque witness carries the minimality
proof; opacity prevents accidental enumeration during proof reduction and
introduces no axiom. This specification is never executed by the production
compiler. No property of Lean's opaque native `Float` is assumed.
`round_zero` proves canonical +0. The addition primitive separately retains
-0 for -0 + -0; both signed-zero cases have checked theorems.

`advance_no_overflow` proves every finite `x+1` lies strictly inside the
nearest-rounding overflow thresholds. The compiled expression therefore
never fails its overflow check. `advance_nearest` bounds its error against
any finite candidate. `advance_exact` gives zero error when the exact sum is
representable. `advance_half_spacing` bounds error by half the width of any
representable bracket containing the sum; adjacent brackets give half an ulp.

`run_exact` proves all samples through a horizon are exact whenever the ideal
samples through that horizon are representable. `Source.solution_unique`
proves uniqueness of the real source solution with the supplied initial value.
`CStatements.real_refinement` bounds the result against any such solution.
The global theorem for all finite starts and counts is:

```text
|value(run x n) - (value(x) + n)| ≤ n
```

This conservative bound includes stagnation at large magnitudes. A frozen
sampler can satisfy this bound alone, but cannot satisfy the complete compiler
contract, which requires the exact relational nearest-even result at every
step. The ODE has no discretization error under exact unit increments; the
numerical error here is rounding. The initial real value is the decoded
binary64 input, not an arbitrary decimal string before host conversion.

## Trusted boundary and coverage limits

* Lean 4.29.1's kernel and the audited standard foundations `propext`,
  `Classical.choice`, `Quot.sound`. No new axioms or proof placeholders.
* Review of the authored Modelica grammar/semantics against MLS 3.7, the C
  grammar/statement rules against C, and encoding/rounding against IEEE754.
  Prose standards are not Lean theorems. This is not CompCert Clight or a
  complete formalization of ISO C's memory model.
* Binary64 `double`, nearest-even addition, gradual underflow, standard
  integer/header meanings and the call ABI. The generated preprocessor checks
  radix, precision, exponent and `FLT_EVAL_METHOD == 0`; these do not prove an
  entire IEEE implementation. The host selects nearest rounding. NaN/Inf,
  other rounding modes, flush-to-zero and unsafe optimizations are excluded.
* Later native C compilation, assembler, linker and hardware. GCC execution
  is tested; there is no composed C-to-machine-code theorem.
* The fixed `ArtifactCheck` file-to-proposition adapter, file I/O, source
  encoding, build orchestration, and host decimal parsing and CSV formatting.
  `examples/driver.c` remains tested support code.

The theorem has an explicit all-behavior preservation shape for this tiny
profile. This does not claim CompCert's language coverage, established C
formalization, optimization/linking proofs, machine-code endpoint or maturity.

## Negative controls

The gate reproduces both artifact attacks from the review: a compiler emitting
`2.0` paired with a certificate containing only `True.intro`, and that same
wrong C paired with a valid complete certificate about a separate good C
file. Both must fail the independent actual-file checker and leave no manifest.
The actual source and EBNF files are also checked independently of candidate
literals and native freshness checks.

Other required controls reject corrupted LR tables/source witnesses, changed C
arithmetic, altered embedded Modelica source and an added logical assumption.
The obsolete executable C reader and its parser-only checks have been removed;
structural printer and grammar uniqueness theorems supply the text connection.
Actual-file mutation and forged-producer controls remain. A renamed Modelica
source with mixed admitted whitespace passes. Native tests cover fractional/negative starts,
subnormals, maximum finite values, signed zero, both even-tie directions,
iteration and malformed inputs. Tests exercise infrastructure and examples;
the theorems quantify over all admitted models, finite encodings and counts.
