# Roadmap to a verified Modelica compiler core

Reviewed **2026-09-13**. **Grammar expansion is blocked.** The numerical
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
| FMI 3 ME/CS | Both interfaces share Solve. Complete termination, time and ME control-call contracts are mandatory and artifact-checked, with composed finite ME control histories; earlier derivative, Float64 getter/setter, reset, nominal/count/version and error-helper contracts remain required. | Remaining public calls, complete histories, static instance ownership, translation-unit and ABI correspondence. |
| Initialization | Creation, entry/exit, rejection and optional logging share the actual static runtime and source IVP. The 801-input full gate and 804-input follow-up package audits passed. | Later host histories and callback frames remain in K02/K03; cross-standard correspondence remains in K05. |
| eFMI | Checked DAE → GALEC → Solve Algorithm → Production C path, method/trace proofs, correlated manifests and actual eFMU certificate. | Cross-standard initialization, coding-guideline evidence and final compliance review. |
| Tensor/AD development | Array source-to-Solve, forward derivative/reverse adjoint foundations and several prepared C contracts are checked. | These are development products; the production compiler still rejects the driven/array profiles. See [tensor plan](tensor-ad.md). |

Latest completed main-workspace gate:
`build/c-factory/me-full-gate-v1.log`, passed with all 829
integration inputs unchanged. It checks the strengthened ME control contracts, static runtime, both
actual FMU interfaces and the eFMU, including the existing native and rejection
controls. Retained artifacts and member comparisons are under
`build/c-factory/me-artifacts-v1/` and adjacent review files.
Compared with `2628f35`, the FMI adapter replaces `calloc`/`free` with 32
permanent ME/CS slots; numerical C, FMI metadata, GALEC and eFMI Production C
are unchanged. Compared with the preceding time artifacts, the
eFMI manifests change only their generation identities and dependent checksums.
The derived termination/release proofs have separate passing FMI/compiler
package evidence for 811 unchanged inputs. No new grammar case is admitted.

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

Next, compose the remaining operation/release histories and actual
concurrent ownership histories. Close callback frames, the no-heap/acyclic call graph and native
profile/layout. The required main gate passed on the 809-input termination
source set; these remaining proofs are still open.
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
  Reset's successful/null calls and reset→initialization composition now use
  the static object interface; arbitrary surrounding histories remain open.
- [ ] Finish public CS communication-time/step arithmetic, status/output
  writes, rollback and repeated-step refinement. Prove progress or rejection
  when binary64 time would stop advancing (including the `2^53` boundary).
  An internal natural-number step counter is insufficient.
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
