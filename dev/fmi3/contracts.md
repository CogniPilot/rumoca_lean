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
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34502115582).
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
header. At the previous checkpoint, 57 of its 75 collected signatures had an unmapped parameter in
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


### Profile-generic render plan

The base scalar, tensor and constant FMI 3 adapters render the same five-piece
C source: the model source-link prefix, the `#include "model.c"` line, a
per-profile declaration preamble, the concatenated helper renderings, and the
concatenated per-signature function renderings in header order. A single
`RenderPlan` structure captures exactly the per-profile inputs of that shape:
the model name (which fixes the source-link prefix), the declaration preamble,
the helper prefix and the per-signature body builder. The generic
`RenderPlan.render` renders a plan, and the render-identity facts are proved once
over an arbitrary plan: `RenderPlan.rendered_functions` (the render equals its
preamble followed by the concatenated rendering of the full function list),
`RenderPlan.rendered_member` and `RenderPlan.rendered_helper` (each signature and
each helper is a located fragment at its actual slot), and
`RenderPlan.render_chars` (the checker certifies each emitted function
separately, joins the character chunks and binds them to the independently read
complete file).

Each profile supplies one concrete plan value: `basePlan` for the scalar profile,
`TensorFunctions.tensorPlan` for the tensor profile and
`ConstantFunctions.constantPlan` for the constant profile. Every profile's
`render` is definitionally that plan's `render`, and the `Runtime`,
`LiteralPreparation`, `TensorFunctions` and `ConstantFunctions` render-identity
theorems, together with the byte-for-byte `adapter_chars`, `tensor_adapter_chars`
and `constant_adapter_chars` lemmas each adapter-bytes certificate instantiates,
are corollaries of this shared development rather than separate copies. A profile
whose adapter fits the five-piece shape supplies a plan value; it adds no
renderer and no render-identity proof family of its own.


### Profile-generic Float64 value-reference dispatch

Every adapter profile's `fmi3GetFloat64` and `fmi3SetFloat64` body shares one
shape: the instance-handle and lifecycle guard, the single-reference request
check, a staged region pointer and element count, a value-reference dispatch,
the count check, and the counted copy loop. Only the dispatch differs between
profiles, and the dispatch itself is one shape: a right-nested chain of equality
guards `if valueReferences[0] == j then <arm> else <next>` over an ordered list
of `(reference number, dispatch arm)` pairs, ending in an "unknown reference"
fallback. The tensor getter covers references `0..4` (time, input, state,
derivative, output), the constant-rate getter references `0..2` (time, state,
derivative), and each setter its writable subset (tensor references `1,2`;
constant-rate reference `1`).

`Float64Dispatch.dispatchChain` builds that chain from the reference list, and
`Float64Dispatch.dispatchChain_printable` proves once, by induction over the
list, that every statement of the chain prints its intended C token grammar,
given that the compared reference expression prints, each arm's statements print,
and the fallback prints. The getter and setter body around an abstract dispatch
statement are `TensorFloat64.getBodyFor` and `setBodyFor`, and the shared
printability of those bodies (`getBodyFor_printable`, `setBodyFor_printable`) is
proved once over an arbitrary dispatch statement. Each profile's `getBody` and
`setBody` are definitionally these shared bodies around the profile's own
dispatch, so per-profile printability and printed-text denotation are the shared
results instantiated at the profile's reference list rather than a body-length
reproof per profile. The constant-rate accessor's function contracts
`ConstantFloat64.get_contract` and `set_contract` keep their statements and are
now discharged by this instantiation. A profile whose accessors fit this shape
supplies its reference list and the printability of its arms; it adds no
value-reference printability or denotation proof of its own.


### Profile record as the single source of truth

One storage `Profile` record carries the per-profile render and call-policy data
of an FMI 3 adapter profile in a single place: the presence of the FMI-visible
input and output regions of an instance record (`hasInput`, `hasOutput`), the
prepared kernel entries the adapter calls with their prototype parameter
spellings (`kernels`), the Float64 getter and setter value-reference dispatch
table (`references`), the extra callees the profile's call policy admits beyond
the shared scalar classification (`extraCallees`), and whether the profile exports
eFMI production artifacts (`hasEFMI`). The tensor profile carries both regions,
the two kernels `rumoca_rhs` and `rumoca_square_jacobian_diag`, getter references
`0..4` and setter references `1,2`, the square-Jacobian-diagonal callee and eFMI;
the constant-rate profile carries neither region, the three kernels
`rumoca_constant_rhs`/`_step`/`_sample`, getter references `0..2` and the single
writable setter reference `1`, the three constant callees and no eFMI. Every extra
callee a profile declares is one of its own declared kernel entries.

`planOf` pairs a profile with the model-derived render inputs (the model name, the
declaration preamble, the reused helper prefix and the per-signature body builder)
to produce that profile's `RenderPlan`. `TensorFunctions.tensorPlan` and
`ConstantFunctions.constantPlan` are definitionally `planOf` of the tensor and
constant profiles, so every render-identity fact continues to flow through the one
shared `RenderPlan` development. The declaration preamble stays a model-derived
rendered string rather than a value recomputed from the profile flags, because the
adapter preamble's byte structure is fixed by the emitted C text, not by the
presence flags alone.

The dispatch table and admitted callees are checked against the profile record.
Each profile's Float64 getter and setter dispatch over exactly the numeric value
references the profile's `references` field declares, in order: the reference
projections of `TensorFloat64.getArms`/`setArms` and
`ConstantFloat64.getArms`/`setArms` equal `referencesOf` of the tensor and
constant profiles. Every extra callee the profile declares (`calleesOf`) is
admitted by that profile's call policy (`acceptedT` for the tensor kernels,
`acceptedC` for the constant kernels). A profile whose adapter fits these shapes
supplies one profile record; the render plan, the dispatch table and the admitted
callees are read from that record rather than restated per profile.


### One adapter-bytes certificate for every profile

The tensor and constant-rate adapter certificates share one certification
metaprogram, `FMI3AdapterCertificate.certifyAdapterBytes`. It takes a
`ProfileCertInputs` record naming the profile's witness model and source,
its render, function-list and helper definitions, its render-identity lemma
(`tensor_adapter_chars` or `constant_adapter_chars`), the rendered declaration
preamble, and a `dischargeContract` step that proves the profile's own
`Contract` from the shared render identity. The shared part certifies the actual
adapter bytes exactly as before: every emitted function gets its own tree and
byte certificate in 256-character blocks, the block-structured concatenation
cursor binds the joined chunks to the independently read file, and the reused
helper prefix and the per-signature bodies are checked against the profile's
function list. What stays per profile is the `Contract` discharge over the
pinned signature list (public API coverage, absent-variable and capability
rejection signatures, and the profile's kernel name exclusions), supplied as a
closure of about twenty lines. `TensorFMI3AdapterCertificate.certify` and
`ConstantFMI3AdapterCertificate.certify` are call sites of the shared entry;
the produced theorem names and statements (`...adapter.contract`,
`Rumoca.CheckedTensorFMI3Files.source_to_build`,
`Rumoca.CheckedConstantFMI3Files.source_to_build`) and the axiom whitelist are
unchanged. A further profile whose adapter fits the shared render shape adds a
`ProfileCertInputs` value and its contract discharge, and no certificate
metaprogram of its own. The base scalar certificate keeps its own entry because
its witness artifact is the compiled scalar source itself rather than a
reconstructed witness.

### One build-artifact driver for the kernel profiles

The tensor and constant-rate build-artifact checks share one driver,
`Rumoca.FMI3ProfileBuildCheck.run`, driven by a `ProfileBuildInputs` record. The
driver independently reads the five staged files, checks the build description,
model description, private `model.c` kernel text and adapter source prefix
against the compiler output, certifies the `model.c` byte assembly from its
render fragments, calls the profile's adapter-bytes certificate, and runs the
final axiom audit. The record supplies what stays per profile: the rejection
label, the checked-namespace base, a compilation closure returning the model
name, model-description tree and kernel `model.c` bytes, the prepared-metadata
identity, the adapter certificate entry, the `model.c` render fragments (the
tensor profile supplies eight, the constant-rate profile three), the kernel
`pieces`/`modelC`/`chars` terms, and an `emitFinal` closure that states and
proves the profile's fixed `source_to_build` contract. The produced theorem
names and statements (`Rumoca.CheckedTensorFMI3Files.source_to_build` and
`Rumoca.CheckedConstantFMI3Files.source_to_build`), the
`verify_tensor_fmi3_build_files` and `verify_constant_fmi3_build_files`
commands, and the axiom whitelist are unchanged. The base scalar build check
keeps its own driver: it certifies the compiled scalar source directly through
the numerical `source_to_c` certificate and carries no private `model.c` render
assembly, so it shares no body with the kernel-profile driver.

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
`build/fmi-types/artifacts/`. The C and GALEC members match the previous checkpoint; only the
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
GALEC members match the previous checkpoint (`code-member-comparison.log`).

### Version call and metadata agreement

The required `Version.FunctionContract` connects the actual `fmi3GetVersion`
function's tokenization and complete typed calls to a constructed literal pool.
`Version.PreparedContract` requires termination at the returned character
address, unchanged memory, immutable storage and readable UTF-8 bytes including
the zero terminator. It has no instance, mode, logger or caller-supplied literal
address premise. The pool describes symbolic static storage, not native linking.

`version_source` composes that mandatory contract with the actual adapter file
and independently denoted model/build XML documents. Both root version
attributes equal the returned `3.0` string. The pinned header declares this same
version, but macro/header interpretation and the native ABI still need their
own bridge. This closes one public-call obligation, not the whole FMI adapter.
All 11 new audit roots and affected packages pass
`build/fmi-version/package-audit.log`. The required full gate passed in
`build/fmi-version/full-gate.log`, with all 637
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-version/artifacts/`; their C and
GALEC members match the previous checkpoint (`code-member-comparison.log`).

### Observable enabled logging

`Logging.FunctionContract` is mandatory in `AdapterContract`. The composed
`logging_source` theorem identifies the actual failure-helper fragment, its
function grammar and prepared internal table, the constructed category string,
and the matching category in the independently denoted model XML.
`ExecutionContract` proves the complete enabled helper call for explicit,
returning importer effects: mode is written before dispatch, all four callback
arguments are evaluated from the actual fields/strings, the invocation is
recorded, and ordinary return produces Error and the host's resulting heap.
Read-only cells, including the category and supplied immutable message, survive.
It does not replace foreign writes with an unchanged-heap assumption.

The reusable event machinery lives in core; C call/return scheduling, symbolic
callee resolution and external effects live in backend-c. FMI supplies the
callback prototype and actual-body theorem. Identifier, field and array
callee accesses are admitted; ambiguous function-designator dereference and
casts are rejected until C function types are modeled. Existing numerical,
loop, literal-lowering and internal-call proofs remain required.

The host effect relation describes completed calls. Its invocation-local return
and uniqueness premises do not guarantee arbitrary importer termination.
Native callback ABI/layout, reentrant hosts, allocation/free, generalized
external expressions and composition through
all public FMI entry points remain open. Source and generated code are unchanged.
All 58 added audit roots and affected packages pass in
`build/c-events/package-audit-v1.log`. The required full artifact gate passed
in `build/c-events/full-gate.log`, with all 646 inventoried inputs unchanged
and both actual archives checked. Retained archives and hashes are in
`build/c-events/artifacts/`; their C, header and GALEC members match the previous checkpoint
(`code-member-comparison.log`). This does not close F02/F03 or permit grammar expansion.

### Complete initialization calls

`InitializationCalls.FunctionContract` is mandatory in `AdapterContract` for
both `fmi3EnterInitializationMode` and `fmi3ExitInitializationMode`. The fixed
actual-file checker proves both exact signatures are in the same collected
table; their printed fragments carry the existing independent tokenization
judgment. The prepared contract covers successful/null calls and every specified
lifecycle/argument failure, with silent and represented returning logger
outcomes. It retains the prior contracts, including literal lowering.

The independent unit policy admits any finite start and an optional finite
stop no earlier than start. The profile has no internal tolerance-controlled
algorithm, so tolerance is unused. `rejects_iff` classifies all raw binary64
arguments; accepted inputs yield a finite argument witness and invalid inputs
reach the helper before time/state writes. Both signed zeros are retained.
The strict `above_iff` policy root is replaced by inclusive `atLeast_iff`, with
all other earlier audit roots and the same axiom whitelist retained.

Successful entry writes the four clock fields, stop/flag and lifecycle mode.
Their old payloads may be uninitialized; only typed writable storage and a
represented kind/Instantiated mode are required. The final heap preserves the
model state and all cells outside those seven writes. Exit changes only the
mode, to Event for ME or Step for this CS profile. Quiet contracts quantify over
heaps, allowing entry/exit composition through the actual intermediate heap.
The resulting clock establishes the existing SetTime reference window.

`initialization_source` retains the numerical source-to-C contract and requires
these same actual fragments, table and literal pool. `SourceExecutionContract`
derives the unique Real source IVP from finite instance storage at the supplied
time origin. It does not assume the source fixes zero; a host setter may choose
the initial state. No initial source equation or new source syntax is invented.

Composition builds in `build/c-initialization/composition-v2.log`; all 51 added
roots and affected package checks pass in `build/c-initialization/package-v1.log`.
The required full artifact gate passed in `build/c-initialization/full-gate.log`,
with all 706 source inputs and the complete file set unchanged. All 13 existing
native FMI groups pass, including the extended argument/atomicity group;
no new test suite was added. Both actual archives are retained in
`build/c-initialization/artifacts/`. Only the FMI initialization-entry body
changes relative to the previous checkpoint; all other C/header/GALEC members match.

| Retained artifact | SHA-256 |
| --- | --- |
| `Integrator.fmu` | `3dc8fbbc535f280afb8d82700d0a5385df2408f6c4fcc5d77b3b6965b0f7402e` |
| `Integrator.efmu` | `6248577590d287e9ad8424329a007e154549b7fe33bc55f3047c586dc22507fc` |

The no-heap requirement changes the remaining creation work to bounded static
instance storage, with complete field initialization and safe slot reuse.
Current generated `calloc`/`free` calls are an open defect (MISRA Dir 4.12/Rule 21.3);
this increment does not remove them. Static creation must establish every
downstream storage/default-state premise. Arbitrary host
ownership/reentry, lifetime, remaining APIs and whole standards/ABI composition
remain open. The symbolic public-call theorem is not a native ABI proof.

### Complete Float64 setter

`Float64Set.FunctionContract` is mandatory in `AdapterContract` for the actual
`fmi3SetFloat64` fragment. The fixed checker establishes membership of its exact
five-parameter signature, including both const array parameters. The contract
uses one actual function table and installed literal pool and retains every
earlier numerical, printer, public-call and artifact obligation. All 51 added
roots and affected package checks pass in `build/c-float64-set/package-v1.log`;
the required full artifact gate passed in `build/c-float64-set/full-gate.log`.
All 694 source inputs remained unchanged throughout the run. Both actual
archives are retained in `build/c-float64-set/artifacts/`; their C, header and
GALEC members match the published the previous checkpoint outputs. No source grammar or
emitted code changes accompany this proof increment.

Independent argument classification covers null instances, empty requests,
lifecycle rejection, invalid lengths/pointers and the first invalid entry.
Validation checks every selected state value for finite binary64 representation
before any state write. Wrong references short-circuit before a value load.
All represented returning logger outcomes, absence of a returning outcome and
disabled logging are characterized by the actual failure helper contracts.

Successful calls preserve accepted payload bits, including signed zeroes.
The ordered writes leave the final request's state value and preserve every
other memory cell. `QuietExecutionContract.set_refines` constructs the finite
input snapshot from accepted raw bits and relates the final heap to
`ModelExchange.setContinuousState`. Its premises describe original storage and
non-aliasing, not a supplied intermediate execution or loop invariant. The
tensor-memory snapshot describes the API buffer; no source array or per-element
IR lowering is introduced.

`Float64SetMetadata.Writable` independently follows a ModelStructure derivative
entry, its numeric reference and the derivative attribute to the same unique
declaration selected by the setter. It requires a scalar continuous local
Float64 state with `initial="exact"` and `reinit=false`, including the pinned
schema's false default when that attribute is omitted. The actual XML permits
precisely reference 1, with the source state name; name uniqueness is not an
assumption. `float64_set_source` binds that XML, the actual printed fragment,
complete calls and event-preserving literal preparation to the same source and
Solve model. The existing numerical source-equation consequence is retained.

This does not establish complete allocation/initialization histories, caller
ownership, native ABI or all remaining public functions. Those obligations and
the complete standards review still block grammar expansion. No source grammar,
runtime, emitter, solver policy or boundary test suite changes in this increment.

### Complete Float64 getter

`Float64Calls.FunctionContract` is now mandatory in `AdapterContract` for the
actual `fmi3GetFloat64` fragment and the shared RHS helper. The fixed checker
proves the getter's exact five-parameter signature occurs in its quoted header
candidates. Earlier public-call, numerical C, printer and literal contracts
remain required. All 58 added roots and affected package checks pass in
`build/c-float64-get/package-v2.log`. The required full artifact gate passed in
`build/c-float64-get/full-gate.log`, with all 686 source inputs and the complete
file set unchanged. Both actual archives are retained in its `artifacts/`
directory; all C/H/ALG members match the published the previous checkpoint checkpoint.

The proof executes both counted loops, including nested numerical C calls, for
arbitrary UInt64 request sizes within the authored size_t semantics. Independent
argument classification covers empty queries with nullable arrays, defensive
null instances, mismatched counts, nonempty null arrays, and the first unknown
reference. The validation loop performs no output writes. Enabled logging
retains every represented returning callback outcome and absent outcome;
disabled logging is silent. Readable reference storage is required only when
validation actually reads it.

Successful queries preserve reference order and duplicates. Each reference
selects the represented time, continuous state or prepared Solve derivative.
The output range uses the existing tensor-memory view; all other cells are
preserved, including model state/time under explicit non-aliasing conditions.
This is an API request buffer of scalar variables, not admission of Modelica
array variables. Tensor-variable serialization will require its own extension.

`Float64Metadata` independently resolves numeric references to unique scalar
continuous Float64 declarations in the actual XML. Its nonempty ASCII decimal
judgment admits leading zeroes; it does not claim the whole XML Schema numeric
lexical space. `metadata_selection` binds C reference selection to those names.
`float64_source` requires that XML, both printed C fragments, the numerical
artifact contract and complete calls for one Solve model, table and literal
pool. Its derivative consequence retains the Real source equation.

The getter theorem assumes represented current state and time. It does not
complete the separate allocation, initialization/start-value or trajectory
invariant. SetFloat64, remaining APIs, native ABI/ownership and complete
adapter composition remain open and block grammar expansion. No runtime,
metadata emitter or source grammar change is made; no test suite is added.

### Complete continuous-state derivative query

`DerivativeCalls.FunctionContract` is mandatory in `AdapterContract`, retaining
every earlier obligation. It binds both the actual public getter fragment and
`model_rhs`, their independent tokenizations and complete calls to the same
prepared Solve model. The fixed actual-file checker proves getter membership
and freshness of all numerical kernel names among the quoted header candidates.
This prevents an arbitrary public signature from shadowing the numerical calls.
Header collection, typedef meanings and native ABI remain separate obligations.

The success proof enters the actual public body, passes the lifecycle and
scalar-access guards, calls `model_rhs`, executes `rumoca_rhs` using the existing
verified C statements and writes the returned finite derivative into caller
storage. It preserves every other cell. Preserving model-state storage requires
the ordinary non-aliasing premise between state and caller output; this is not
silently assumed in the general frame theorem. No solver step or time advance
occurs in this getter.

The same contract characterizes defensive null handles, every rejected declared
lifecycle state, wrong UInt64 counts and null buffers. Error prefixes reach the
actual failure helper before output access or numerical evaluation. Enabled
logging includes every represented returning callback effect and absent outcome;
disabled logging is silent and permits a null logger. Valid caller/instance
storage and native host realization retain their explicit boundaries.

`DerivativeMetadata` independently resolves the XML's ordered derivative entries
to unique derivative and scalar continuous state declarations. Its state
projection agrees with `StateMetadata.OrderedStates`. `derivative_source`
requires that actual XML order, both adapter fragments, the numerical C contract
and eventful literal preservation for the same constructed pool. The separate
`derivative_call_source` theorem connects the public output to the Real source
equation using existing Flat/DAE/Solve preservation.

All 41 added roots and affected package checks pass in
`build/c-derivatives/package-v1.log`. The required full artifact gate passed in
`build/c-derivatives/full-gate.log`, with all 675 inventoried inputs unchanged.
Both actual archives and hashes are retained in `build/c-derivatives/artifacts/`;
their C, header and GALEC members match the previous checkpoint (`artifacts.log`).
No source, renderer, metadata or initialization policy changes; no new test suite
is added. Native headers/ABI, ownership/allocation, complete initialization and
remaining public APIs still block the whole-adapter claim and grammar growth.

### Continuous-state getter and setter

The next increment requires `StateCalls.FunctionsContract` in `AdapterContract`
for both actual state accessor fragments. All earlier fields are retained.
The fixed checker must prove both signatures occur among the actual header
candidates. `state_access_source` connects their bytes, independent function
tokenization, definition table, literal pool and XML state order to the same
compiled source and prepared Solve model.

The contract covers successful getter/setter calls and defensive null handles,
every rejected declared lifecycle state, incorrect counts, null buffers and
non-finite setter inputs. Enabled errors retain all represented returning
callback effects and absent outcomes; disabled logging is silent. Reusable
guard and scalar-access proofs derive these paths from independent argument
conditions. No caller supplies a selected successful body execution as a premise.
Enabled logging requires a bound callable logger; disabled logging permits a
null logger. FMI §2.3.1 permits null callbacks but leaves use of the unavailable
functionality undefined. Native callback realization remains outside this proof.

Successful reads preserve the finite state's exact bits, including signed zero,
and its represented Model Exchange state. Successful writes implement
`ModelExchange.setContinuousState`; both have frames for every other cell.
Valid storage and the existing finite state invariant remain explicit premises.
These functions expose/update state; they do not choose a solver or prove that
arbitrary importer-selected values form a solution trajectory.

`StateMetadata` independently follows ordered derivative references to unique
scalar continuous Float64 state declarations. Both reference resolution and
the resulting ordered list are functional. State identity is independent of
nominal values and initialization attributes. Array serialization is outside
this scalar judgment and will need its own verified mapping.

All 39 new roots and affected package checks pass in
`build/c-state-calls/package-v1.log`, including the composed source theorem.
The required full artifact gate passed in `build/c-state-calls/full-gate.log`,
with all 667 inventoried inputs unchanged and both actual archives checked.
Retained archives and hashes are in `build/c-state-calls/artifacts/` and
`artifacts.log`; every C, header and GALEC member matches the previous checkpoint.
Native header/ABI correspondence, allocation,
complete initialization, callback realization and the remaining public APIs
still block the whole-adapter claim and grammar growth. See the
[standards review](../standards-review.md#continuous-state-access-standards-impact).

### Complete nominal queries

`Nominals.FunctionContract` is now mandatory in `AdapterContract`, retaining
all earlier fields. The actual-file checker kernel-checks the nominal signature's
membership in the collected header candidates. `nominals_source` binds the
same actual function fragment, definition table, constructed literal pool and
eventful literal-lowering contract to the compiled Solve model and actual XML.

The complete-call proofs cover allowed queries, null instances, rejected
lifecycle states, wrong counts and null output buffers. Successful calls write
exactly binary64 one and frame every other cell. `stored_default` decodes this
as the positive real value 1. Rejected calls use both actual failure strings and
the same enabled/disabled logging machine; all represented callback outcomes
and absent outcomes are retained. `query_cases` exhausts the argument/lifecycle
cases under the corresponding memory and host premises.

`NominalMetadata.OrderedNominals` independently follows ordered
ContinuousStateDerivative entries through unique derivative/state references.
It checks scalar continuous Float64 variables with neither explicit nor
inherited nominal information. Its actual-XML contract identifies the compiled
source state and the same decoded value 1. This is a scalar nominal/order
judgment, not whole-schema compliance; arrays require their own volume and
serialization interpretation. No source syntax or emitted bytes change.

All 33 new audit roots and affected packages pass in
`build/c-nominals/package-v2.log`. The required full `lake test` gate passed in
`build/c-nominals/full-gate.log`, with all 660 inventoried inputs unchanged.
Both actual archives are retained in `build/c-nominals/artifacts/`; their C,
header and GALEC members are unchanged from the previous checkpoint. Writable output
storage, well-formed instance fields, admissible logger bindings and atomic host
effects remain explicit premises. Native header/ABI correspondence, allocation,
host ownership and remaining public APIs still block F02/F03 and grammar growth.
See [the standards review](../standards-review.md#nominal-queries-standards-impact).

### All failure-helper outcomes

`Logging.FunctionContract` now also requires `AllPreparedContract` and
`SilentPreparedContract`. The enabled contract quantifies over every outcome
in the importer effect relation without requiring existence or uniqueness.
Each returning outcome records the actual invocation, returns Error and retains
the host's resulting heap. If there is no outcome, the atomic external machine
is stuck; this case is included explicitly. The disabled contract proves empty
events, Error and exactly the mode write with arbitrary unused foreign bindings.
`logging_source` requires these guarantees for the same actual helper fragment,
internal table and constructed literal pool as its existing grammar, XML and
eventful literal-lowering contracts.

Generic silent-prefix equivalence preserves faults and finite/infinite divergent
histories. Shared C characterizes all external choices with a proved return
continuation. FMI proves the helper's dispatch and resume paths; the earlier
determined-result proofs reuse these paths and follow from the new contract.
Immutable category/message storage survives every returning effect. The formal
model still does not execute inside host calls or establish native ABI,
allocation or complete public-entry composition. FMI prohibits log callbacks
from calling back into the FMU; this admissible-host restriction still needs to
be connected to the native boundary, rather than treated as required FMU support
for reentrant logging. See [FMI 3.0.2 §2.2.1](https://fmi-standard.org/docs/3.0.2/).

The implementation and compiler composition build in
`build/c-logging-choices/promotion-v2.log`. All 21 additional audit roots and
affected package checks pass in `build/c-logging-choices/package-audit.log`;
every earlier audit root is retained. The required full artifact gate passed in
`build/c-logging-choices/full-gate.log`, with all 654 source inputs unchanged
throughout the run and both actual archives checked. Retained archives and
hashes are in `build/c-logging-choices/artifacts/`; their C, header and GALEC
members match the previous checkpoint (`artifact-retention.log`).
No grammar, emitted code or test suite changes.
F02/F03 remain open.

### Eventful literal lowering

`LiteralPreparation.EventContract` is mandatory for the same actual adapter
function table. Successful preparation supplies `EventPreparedContract`: all
string syntax is replaced, and all complete-call behaviors agree before and
after the pass. Symbolic function addresses, foreign relations, converted
arguments, heaps and event labels are preserved. Divergence and faults are
included; foreign determinacy and successful execution are not premises.

Shared C owns the two bisimulations and pool composition. FMI derives their
name/shape-of-call premises from the actual collected functions. Existing
ordinary-call proofs specialize the shared scheduler lemmas. The compiler's
`literal_events_source` and `logging_source` bind these guarantees to the
independently read adapter and its successfully constructed pool. Emitted C
bytes are unchanged. Native static linking, header/ABI interpretation and the
public-entry/foreign-execution gaps above remain separate. All 37 new roots
and affected package checks pass in `build/c-events/literal-package-audit-v1.log`.
The required full gate passed in `build/c-literal-events/full-gate.log`, with
all 651 inputs unchanged and both target archives checked. Their C, header
and GALEC members match the previous checkpoint; artifacts and comparison evidence are retained
in `build/c-literal-events/`. This does not close F02/F03.

## Development tensor source-build checker

The pointwise tensor profile adds a parallel fixed actual-file checker,
`verify_tensor_fmi3_build_files`, kept out of the CLI's production admission. It
reads the same five staged files (`sources/model.c`, `sources/fmi3.c`,
`sources/buildDescription.xml`, `modelDescription.xml` and the source snapshot),
compiles the source with `compileTensor`, and discharges the obligations of
`Rumoca.TensorSourceBuildContract`: the actual `model.c` bytes equal the
certified tensor kernel text and carry the pointwise IVP artifact contract; the
build and model-description bytes are the prepared XML documents; the actual
`fmi3.c` satisfies `FMI3.TensorAdapter.Contract` for a scalar witness sharing the
model name, kernel-checked against `TensorFunctions.render` with the same
per-function tree-equality and maximal-munch tokenization machinery as the scalar
adapter certificate, generalized over the tensor function list; and the model
identifiers and instantiation token agree with the tensor model description. It
emits `Rumoca.CheckedTensorFMI3Files.source_to_build` under the same
`propext, Classical.choice, Quot.sound` whitelist and is registered as the
`tensor-fmi3` certificate kind. Native compilation, ZIP transport and the FMPy
importer remain the same boundaries as for the scalar path.
