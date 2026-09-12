# FMI 3 proof boundary

The selected release product is one FMU containing both Model Exchange and
Co-Simulation, as permitted by FMI 3.0.2 §2.5.2. Both interfaces describe the
same variables. A CS instance uses the shared model kernel through its internal
solver; it does not invoke ME-only FMI entry points on a CS instance.
The normative reference is [FMI 3.0.2](https://fmi-standard.org/docs/3.0.2/).

The source-build correction for SR01 now has a separate checked obligation.
Shared Linux/GCC recipes produce both `buildDescription.xml` and the native
argument list. Independent decoded requirements check platform selection,
compiler, C11/floating-point options, source files and the external math library.
The actual-file `FMI3.SourceBuildContract` composes those XML character/recipe
proofs with the complete existing numerical C contract. The publication gate
checks the staged files before native compilation; the existing rebuild uses
the XML and a separate loader process to catch unresolved symbols. Six new
axiom roots and the targeted artifact gate pass in `build/fmi-build-package.log`
and `build/fmi-build-artifact-gate.log`. The required full gate passed in
`build/fmi-build-full-gate.log` and
[CI for f1ce838](https://github.com/CogniPilot/rumoca_lean/actions/runs/34502115582).
Native compiler/linker behavior and the other
metadata/runtime/archive obligations below remain outside this increment.

The SR02 increment preserves the complete numerical contract under a proved
internal-linkage printer and single compiled adapter translation unit. Its
source/build/ME/CS identities derive from the same parsed model name, with a
validity proof and injectivity for distinct names. The actual-file proposition
additionally observes the two model-description identities and exact adapter
prefix/include fragment. At that checkpoint its remainder was unconstrained;
the complete-adapter contract below now binds those bytes too. Preprocessing
and linker behavior still require their separate bridges.
Thirteen new roots pass `build/fmi-linkage-package.log`. The actual-file,
importer, two-source-link, mutation and failure-preservation gate passes in
`build/fmi-linkage-artifact-gate.log`. These checks also pass in the current
required full gate, `build/fmi-functions/full-gate.log`.

These are acceptance obligations, not declarations of existing theorems.

| Contract | Required statement |
| --- | --- |
| Source → Solve | Adjacent equation, initialization, output and numerical-policy proofs compose to the original parsed model |
| Solve → production C | Every behavior of the actual emitted C kernel refines the prepared Solve program under the stated memory and arithmetic contract |
| ME conformance | Calls allowed for the advertised ME profile obey the reference state machine and return the model's variables, continuous states, derivatives and event information |
| CS conformance | Calls obey the CS state machine; accepted steps refine the selected internal solver; Float64 communication time, progress, rollback and status outputs are covered |
| Error/lifetime conformance | Invalid calls and arguments have the required status and subsequent lifecycle behavior; allocation, reset, free and instance isolation obey the memory contract |
| Metadata conformance | Variable identities, types, dimensions, starts, derivatives, dependencies and capabilities are projections of the same executable root used by C |
| Artifact binding | The checked proposition covers the actual source, grammar, C members, XML and archive inventory; a producer cannot substitute a different theorem or kernel |

The capstone is a composition of these contracts. It is unnecessary to prove
production C directly against every earlier IR again, but the public compiler
theorem must actually invoke the adjacent proofs. FMI compliance is an
additional refinement of the runtime API, not a consequence of preserving the
derivative function alone.

The FMI reference semantics must be written independently of the implementation
and reviewed against the standard. Defining compliance as equality to our own
dispatcher would not establish standard conformance. Official XML schemas,
independent importer runs and direct ABI negative tests provide additional
conformance evidence; they do not replace the theorem. Native C compilation,
linking, headers/ABI and packaging tools remain explicitly classified until
their own bridges are proved.

Only implemented capabilities are advertised by development artifacts; a
verified release also requires their proofs. The current unit FMU advertises
ME and CS with an internal step of 1 and no optional capabilities. Its adapter
is tested, not fully verified. The next planned CS method is unit-step integration with
piecewise-constant input; arbitrary step sizes require additional arithmetic
and time proofs. Finite `x + u` can overflow, and finite `time + 1` can stagnate.
Neither fact is handled by the existing unit-derivative/no-overflow theorem.
Initialization must also preserve the declared `fixed=true, start=0`
constraint. Any importer override of that initial state needs an explicit
configuration semantics and preservation proof; derivative preservation alone
would not justify it.

The production unit FMU remains separate from that next profile: its source
has no initialization modifier and the existing source contract permits any
finite initial state. The metadata supplies zero as the default, with finite
host overrides. Its CS adapter rejects fractional/nonprogressing communication
steps without advancing, checks the declared stop time, and delegates each
accepted integer step count to the existing verified kernel. The Float64 time
and C-memory bridges are still open. See `docs/verification.md` for the exact
implemented boundary and `tests/fmi3.py` for independent ABI evidence.

Partial body proofs now cover ME state access, the ME derivative getter and
the internal model-advance helper. The call model executes both emitted helper
bodies and the previously verified numerical C statements, with checked
parameter/return conversions and a full final-heap observation. The internal
advance theorem quantifies over finite states and uint64 counts. It does not
prove the public CS communication-time checks, statuses or lifecycle. Actual
adapter text, correlated XML, memory layout, logging and lifetime still need
their own bridges before the capstone above can be claimed.

The ME time setter now has a successful-body theorem and an exact guard/window
equivalence over finite binary64 values. The reference window records start,
second-last completed-step and last event-entry bounds, plus an optional stop.
The generated history blocks now have universal execution, representation and
frame theorems. A separate `eventTime` field avoids retaining obsolete
completion bounds. Complete successful event-entry and completed-step bodies
now have all-behavior contracts, including mode/Boolean writes, model-state
preservation and composition with the reference history. Output ownership and
typed writable storage are explicit; the two completion outputs may alias.
`InitializationBodies.exit_correct` also covers the complete successful
initialization-exit body for both ME and CS: every behavior returns OK in the
reference next mode, preserving model state and clock history. Its frame
theorem preserves all other memory. Instance bindings, a valid interface kind
and the writable initialized mode cell are explicit premises; public ABI entry
and printed bytes are separate obligations. The seven new theorem roots passed
`lake build check-fmi3` in `build/fmi-initialization-exit-package.log` with the
existing axiom whitelist.

`InitializationEntry.correct` now proves the successful initialization-entry
body for both interfaces, including the actual argument guard, clock writes,
stop/flag stores, lifecycle mode and status return. It preserves model state
and establishes both reference history and the represented `SetTime` window.
The independent core admission predicate is equivalent to the guard for finite
start and arbitrary optional argument encodings. Undefined arguments may hold
NaNs; stop and flag cells may be uninitialized before the writes. Typed writable
clock/mode storage and supplied parameters remain premises. The package audit
passed in `build/fmi-initialization-entry-package.log`.
`InitializationEntry.then_exit` composes these two successful bodies through
the exact shared heap and proves final mode, history and model preservation.
The aggregate audit passed in `build/fmi-initialization-entry-audit.log`.

The runtime's finite positive tolerance and strictly later stop policy still
needs review against FMI 3.0.2 §2.3.2; the theorem states this policy explicitly
and does not label it complete normative conformance. General lifecycle
composition, rejected-call/logging bodies and allocation/lifetime still need
proofs. Nonfinite start is outside this successful-body theorem. Nonfinite ME
query times have a
guard-rejection theorem, not yet a complete logging/Error-return theorem.
The comparison model includes signed zeros, infinities and unordered NaNs;
floating exception flags and traps remain outside its observation model.

`LifecycleGuard.reference` now proves the guard equivalence in the shared C
memory/execution model, for every existing command, kind and represented mode.
`require_run` executes the actual three-step prefix, preserving the whole heap;
`accept` reaches the continuation and `reject_prefix` reaches the emitted
failure call. The instance binding, fresh local and readable kind/mode fields
are explicit. Initialization entry/exit and the event/completed-step prefix use
this common result through exact-state block composition. The shared C and FMI
audits passed in `build/fmi-lifecycle-guard-package.log`.
This closes the general prefix bridge, not the failed-call/logger execution or
the actual printed-adapter/ABI contract. No command, grammar, solver or
numerical policy was added.

## Error-state correction

The 2026-09-10 standards review found a concrete mismatch: the private error
mode prevented reads after an error, and ME getter guards excluded
`terminated`. FMI 3.0.2 §§2.3.1 and
[2.3.8](https://fmi-standard.org/docs/3.0.2/#state-terminated) require the error
transition to `Terminated` and allow final-value queries there, including ME
states, derivatives, nominals and event indicators. Values after an error are
for debugging. The existing `allowed_correct` theorem proves agreement with
our authored predicate; this finding shows why that alone cannot certify FMI
conformance.

The private mode is removed, the independent predicate and emitted guards
agree on the corrected states, and `fail` now writes `terminated`.
`LifecycleBodies.terminate_correct` covers every behavior of the successful
termination body, including final mode and model/history preservation.
`failure_mode_run` executes the actual error helper's mode write, leaving the
logger and Error return in its continuation. The state and derivative getter
proofs use the general lifecycle theorem and now cover Terminated too.
The core/C/FMI package checks passed in `build/fmi-termination-package.log`.
The existing ABI tests now require post-error reads and final ME queries;
the actual combined FMU passed `lake run fmi-test` in
`build/fmi-termination-artifact.log`, keeping thirteen test groups. Callback execution, full failed-call
returns and actual adapter-byte binding remain separate required proofs.

## Reset and complete adapter bytes

The current reset increment connects the compiled model's selected initialization
to the complete typed `fmi3Reset` call. `Reset.Storage` requires allocated,
writable cells of the declared types; their old values may be uninitialized or
nonfinite. For both interface kinds and every declared lifecycle mode, the call
terminates with OK, writes the prepared positive-zero state, clears the clock
and stop fields, and returns to Instantiated. Its frame theorem preserves all
other cells, including other instances. A null instance returns Error without
changing memory. The source consequence uses the value loaded from the returned
heap and the same compiled artifact's initialization plan. Its supplied source
start time is prospective; reset itself clears the stored clocks to zero.

`Reset.Syntax` independently specifies the complete function's tokens and C
literal. `Reset.FunctionContract` combines that syntax with all call behaviors
in the actual rendered definition table, requiring the fixed signature and
unique function names. `FMI3.AdapterContract` adds exact equality between the
complete adapter file and that table's renderer. The fixed actual-file checker
requires this contract in addition to the prior numerical, build-description
and identifier contracts. Candidate signatures and rendered character chunks
have no proof authority: Lean checks each function's printer equality, their
concatenation against the independently read file, and the final axiom closure.

The follow-on `Reset.Printer` certificate instantiates the shared expression,
statement and function grammar directly on the emitted CTree. The strengthened
`FunctionContract.genericSyntax` requires that judgment for the certified text,
alongside the previous contracts. `adapter_reset_syntax` identifies its exact
fragment in the actual adapter file. The typedef context names the three types
used by reset; it does not prove their header declarations or ABI meanings.
At that checkpoint cross-category longest tokens, adjacent-string concatenation
and the remaining translation-unit obligations stayed open. All 85 new roots
and the affected packages pass, and the required full gate passed in `build/c-token/full-gate.log`
with all 613 inputs unchanged. [c-printer.md](../c-printer.md) records its evidence.

The next increment adds `FunctionContract.tokenization`. It requires the
normal-context longest-token and ordinary-literal concatenation consequences
on the same function grammar witness, while retaining all previous fields.
`adapter_reset_tokenization` exposes the certified fragment's position in the
actual file. The cross-category and comment-boundary proofs are reusable
across all admissible shared CTree functions. All 67 new roots and affected
packages pass `build/c-lexical/composed-audit.log`. The required full gate
passed in `build/c-lexical/full-gate.log`, with all 621 inputs unchanged and
both actual archives checked. Exact artifacts are retained in its `artifacts/`
directory. Header-name/directive contexts, macro expansion, type/scope
constraints and the other functions still need their own composition.

The complete-function-section increment now requires that composition for
every runtime function and helper. `AdapterPrinter.FunctionsContract` locates
the entire section after the exact fixed adapter preamble. The shared list
theorem retains function boundaries, maximal tokens and ordinary-literal
concatenation in one grammar witness. The actual checker kernel-checks the
collected signature spellings using the reusable C certificate builder.
`AdapterContract` retains all previous fields; `adapter_reset_source` composes
the new section grammar with the reset behavior/source result for the same
definition table. Nine new roots and affected packages pass
`build/fmi-functions/package-audit-v2.log`. The fixed actual-file checker passes
in `build/fmi-functions/actual-fmi.log`. The required full gate passed in
`build/fmi-functions/full-gate.log`, with all 625 inventoried inputs unchanged
and both actual archives checked. Exact artifacts and hashes are retained in
`build/fmi-functions/artifacts/`.
The supplied typedef-name context does not establish
actual declarations or type meanings, and the other public calls still need
their execution contracts.

The same review inspected adjusted parameter spellings from the actual pinned
header. At `fe4ebef`, 57 of its 75 collected signatures had an unmapped parameter in
`FMI3.cTypes`, spanning 43 spellings (`build/fmi-functions/signature-types.log`).
These include `size_t *`, `fmi3Boolean *`, value-reference pointers and callback
aliases. The isolated universal result in `unmapped-call-v2.log` confirms that
that revision's typed machine could not enter `fmi3GetNumberOfContinuousStates`
with its intended pointer arguments because `size_t *` was absent. This is an open
F03 execution-model obligation, not a generated native C failure; the existing
native FMI checks pass. The next contract work must cover those conversions
and their header/type correspondence without weakening the current guarantees.

This is a complete byte binding and a reset execution contract, not an execution
proof of every function in the containing translation unit. Preprocessing, official
header meanings, global storage, allocation/lifetime, callbacks, other public
calls, native ABI and the complete FMI archive contract remain open. The header
collector only proposes signatures; its new tail-recursive comment reader is
proved equivalent to the earlier restricted reader, not to full C syntax.
Reset provenance maps and original-to-staged source identity remain separate.

The 27 added audit roots, existing package audits, focused printer certificate
and reset-value mutation check pass. The complete fixed actual-file check also
passes in `build/fmi-reset/actual-file.log`, including the final source-build
contract's unchanged axiom audit. The required main-workspace `lake test` gate
also passed in `build/fmi-reset/full-gate.log`, with all 529 inventoried inputs
unchanged and both actual target archives checked. The broader adapter and
standards obligations above remain open.
The existing FMI boundary suite adds one mutation of the reset value while
preserving the numerical file and API prefix. Character composition reuses the
existing `CString.join_toList` theorem before kernel reduction, avoiding the
cost of reducing complete intermediate strings in each function certificate.

The subsequent shared printer increment strengthens `AdapterContract` with
character stability of the complete actual adapter file. The generic CTree
theorem composes every expression, statement and function; its FMI instance
also covers the prefix, declarations and helpers. Source lexical rules establish
model-name safety, while the kernel checks the quoted signature spellings.
`adapter_preprocessed` exposes stability under the modeled trigraph and splice
rewrites. This does not interpret macros, included headers or other public calls.
All 35 new roots and the affected packages pass in
`build/source-cutover/build/c-printer/composed-package-audit.log`. The fixed
checker passes on the retained FMU files in that directory's `actual-fmi.log`.
The required main artifact gate passed in `build/c-printer/full-gate.log`, with
all 596 inventoried inputs unchanged and both actual archives checked;
see [the generic printer roadmap](../c-printer.md).
Complete-file assembly composes kernel-checked segment equalities against the
independently quoted input, including EOF. This replaces a large recursive
equality check that overflowed during the first required gate, while retaining
the same proposition and axiom policy.
No grammar, solver or emitted C behavior changes in this increment.

## Rendering decision

Use ordinary Lean functions over typed target representations, followed by
small printers. Do not add a general template engine while this core is being
verified. Target syntax and metadata should remain readable and testable, with
escaping and binding owned by their representations. This preserves a direct
proof path from prepared Solve/runtime programs to emitted code.

A later Rust/MiniJinja producer could remain untrusted and submit its actual
output to the independent Lean checker. It would still need a target semantics
and artifact contract; textual substitution alone cannot inherit correctness.
That extension is deferred and must not complicate the current FMI milestone.


### Parameter coverage and actual call entry

The follow-on increment adds all adjusted pointer spellings missing in the
57-signature review, plus unsigned 32-bit `fmi3ValueReference` conversion. Shared
`CallSignature` proves fresh scope construction and coherent typed entry for
arbitrary parameter lists and convertible arguments; it also supplies argument
witnesses for every known type. `CallTypes` instantiates this for the exact
runtime helper/API list and the renderer's definition lookup.

`AdapterContract` now requires every listed function's parameter names to be
unique and all parameter/return types to be known (with `void` returns allowed).
The fixed checker proves readiness of the collected signatures in Lean's kernel.
`adapter_call_entry` retains actual-byte identity and independent function grammar
while deriving entry for every member and convertible argument list. The heap
and saved continuation are unchanged at entry. All prior reset, grammar and
preprocessing fields remain required.

Pointer aliases and callback parameters have opaque address values here; this
is not a proof of pointee types/layouts, callback execution or native ABI. The
unsigned relation proves the chosen dictionary's conversion semantics, not the
meaning of parsed official headers. Complete body behaviors, allocation and
whole-translation-unit interpretation remain open. All 26 new roots and affected
packages pass `build/fmi-types/package-audit-v2.log`. The signature review reports
zero missing parameter types among 75 APIs. The strengthened actual-file checker
passes in `build/fmi-types/actual-fmi.log`. The required full artifact gate passed
in `build/fmi-types/full-gate.log`, with all 629 inventoried inputs unchanged and
both actual archives checked. Exact artifacts and hashes are retained in
`build/fmi-types/artifacts/`. The C and GALEC members match `fe4ebef`; only the
authored target semantics and mandatory proof contract are strengthened.

### Count calls and correlated metadata

`CountQueries.FunctionContract` covers complete typed entry and every behavior
of both existing ME count functions. Success returns OK and writes one
continuous state or zero indicators, preserving every other cell. Null
instances return Error with unchanged memory. Invalid lifecycle calls and
missing output pointers return Error and enter Terminated when logging is
disabled. `CountQueries.prepared_failure`
constructs the message addresses and immutable storage from the exact rendered
function list. Native allocation and enabled callbacks remain open.

The actual `AdapterContract` now requires both count contracts and a successful
literal-pool construction in addition to all its earlier obligations.
`SourceBuildContract.metadata` binds the complete actual XML document to the
same compiled Solve preparation; previously only its public identifiers were
in that final proposition. The independent scalar count relation resolves
ModelStructure references to unique continuous Float64 declarations with no
Dimension children, and rules out duplicate selected references. Future arrays
must supply a volume interpretation; counting array declarations is insufficient.

`counts_source` joins actual-file function grammar, all success behaviors,
returned storage, Solve state volume and the actual metadata count relation.
`counts_failure_source` retains the same artifact/table witness while
constructing static storage and characterizing both failure paths. The exact
C/IEEE dictionary and symbolic memory premises remain visible. This does not
close the whole-adapter, header/ABI, allocation, callback or standards contract.
All 28 added roots and affected package checks pass
`build/fmi-counts/package-audit-v2.log`. The strengthened actual-file checker
passes in `build/fmi-counts/actual-fmi-v2.log`. The required full gate passed in
`build/fmi-counts/full-gate.log`, with all 634
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-counts/artifacts/`; their C and
GALEC members match `d147774` (`code-member-comparison.log`).
