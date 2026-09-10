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
and `build/fmi-build-artifact-gate.log`. Full-gate evidence is tracked in
`build/fmi-build-full-gate.log`. Native compiler/linker behavior and the other
metadata/runtime/archive obligations below remain outside this increment.

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
