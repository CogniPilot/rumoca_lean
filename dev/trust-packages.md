# Trust work packages K02-K05

Status: 2026-09-25 at `d53bd0e`. All four packages are **open**. This document
is the authoritative definition of the K02-K05 exit criteria; the ledgers that
say "K02-K05 remain open" ([trust-ledger.md](trust-ledger.md),
[standards-review.md](standards-review.md), [misra-c-2025.md](misra-c-2025.md),
[verification.md](../docs/verification.md)) refer here.

**Gate rule.** No Modelica or GALEC grammar spiral stage and no release may be
accepted while any K02-K05 exit item below is open. The N01 repair (GALEC error
signaling, [standards-review.md](standards-review.md)) is the one admitted
exception: it repairs an existing finding and adds no source case. A second
exception (user decision, 2026-09-25): recognition-only grammar slices toward
`Modelica.Blocks.Sources.Constant` may be accepted while K02-K05 items are open,
provided each slice keeps every published artifact byte-identical (admission
of anything new remains a semantic rejection with a certified rejection) and
passes its own review and the required gate. Admitting the block as a fourth
FMU waits until K02-K05 and the open findings SR08-B, SR10-SR12 and S01 cover
it. Each item
closes only with its stated evidence for the whole frozen subset (Integrator,
TensorSquare and ConstantRates FMUs; Integrator and TensorSquare eFMUs) and a
passing `nix develop .#verification --command lake test`. A package-level
audit, native run or analyzer pass alone closes nothing.

Legend. Status: **done** (evidence cited, item closed), **partial** (evidence
cited, stated remainder open), **open**. Size, in gated slices (one emitter or
contract change with its full gate): S (under one), M (one), L (two to four),
XL (more than four). Kind: proof, emitter (bytes change), native (host
evidence at the trusted boundary), doc.

**Current gated baseline.** Latest full gates, each exit 0 with post-audit 0:
`build/count-condition-gate/full-v1` (`8a4a433`),
`build/fold-terminal-gate/full-v1` (`630ef4a`),
`build/galec-cutover-gate/full-v1` (`8a3a513`),
`build/galec-unify-gate/full-v1` (`26a7be5`),
`build/misra-isfinite-gate/full-v1` (`6e8c5b8`; 2,664 inputs, 9,164 axiom
reports, three 75/75 FMI matrices, zero discrepancies). **Pending, not
done:** N01 (`build/wt-n01`, six commits `aae7ab5`..`de480f9` on `6e8c5b8`;
tensor eFMI DoStep product/sum preflight and `OVERFLOW` signal). No required
gate result exists for N01; no item below counts N01 evidence.

## K02 - Static instance storage without dynamic allocation

Definition. Every FMI 3 instance lives in a fixed array of fully typed
`Instance` records whose storage exists for the whole execution; reservation
uses atomic flags. No generated function, transitively, reaches an allocation
entry point. A custom allocator over a static byte arena does not satisfy
Dir 4.12. Multiple independent ME/CS instances are preserved; exhaustion,
initialization failure and slot reuse follow FMI 3.0.2 without an unstated
serialization restriction or silently changed capability flags. The eFMI
Production Code operates only on caller-supplied state and remains callable
from an RTOS task.

- **K02.1 Storage contract and capacity. Partial.** Emitted pool of
  `StaticStorage.deploymentCapacity = 32` slots (`StaticStorageCode.lean`);
  declarations proved and printed by `StaticStorage.records_mean`,
  `StaticStorage.printed`, `StaticStorage.declarations_initialize`; quiet and
  logged exhaustion in the factory contracts. Remaining: record capacity as a
  stated product parameter with its FMI consequence (exhaustion returns NULL,
  capability flags unchanged) in [fmi3/contracts.md](fmi3/contracts.md). S, doc.
- **K02.2 Reservation helper. Done.** `StaticSlots.reserve_iff`,
  `cannot_reserve_twice`, `full_iff`; `AtomicSlots.reserve_corresponds`,
  `scan_reserves`, `release_exists`; production binding
  `StaticRuntime.reservation_bound`, `factory_bound`, `release_bound`.
- **K02.3 Activate/initialize/deactivate, ownership, isolation, full reset on
  reuse. Partial.** Done: lease ownership `SlotOwners.only_owner_releases`,
  `reserved_excludes`; other-slot isolation `StaticReset.restarted_other_instance`,
  `restarted_owners`; `StaticStorageCalls.initial_create_release`;
  annotated concurrent lease histories `ConcurrentSlots.source_slot_histories`,
  `ReservationRegistry.source_reservation_histories`. Open:
  (a) **defect**: TensorSquare instantiation writes neither `u`, `dx`, `J` nor
  `stop`/`stopDefined`, and `fmi3Reset` leaves `u`, `dx`, `J`; ConstantRates
  leaves `dx`, `stop`, `stopDefined`. A reused slot therefore exposes the prior
  instance's values instead of the `modelDescription.xml` start values
  (bytes: `build/misra-isfinite-gate/full-v1/TensorSquare-fmi3.c`
  instantiation). Repair: fill every FMI-visible region from prepared start
  values in `TensorInstanceInit`/`TensorReset` and constant counterparts, plus
  an independent "factory writes every `Instance` member" predicate over the
  layout names. M-L, emitter+proof. (b) Derive the concurrent lease annotations
  for every factory path instead of assuming them. L, proof. (c) Native
  `<stdatomic.h>` lock-free correspondence stays a named boundary. S, native+doc.
- **K02.4 Creation/release supply every downstream premise. Partial.**
  Scalar: done; `FMI3.adapter_termination_release`, `CSProtocol.correct`,
  `MEProtocol.correct` start from actual creation and end in release to the
  original owners. Tensor: `TensorLifecycleHistory.lifecycle_from_creation` and
  `lifecycle_cs_step` still take the reached heap, finite kernel execution and
  reservation representation as premises. Constant: factory/free contracts
  only. Remaining: tensor and constant creation-to-release derivations with no
  supplied storage or successful-call premise. L, proof (after K02.3a).
- **K02.5 Layout, size, alignment and handle mapping bound to bytes and the C
  profile. Open.** `StaticStorage.records_mean` fixes record shapes and member
  types; `CMemory.Address` separates nested aggregates (MC10). No size,
  alignment or padding model exists. Remaining: a pinned C-profile layout
  model for the admitted types and a theorem that the symbolic cell layout is
  realizable at the emitted declarations, or an explicit native-boundary record
  with a host layout check extended in `tests/fmi3.sh`. L, proof+native.
- **K02.6 Checked no-heap, acyclic call graph over all generated code.
  Partial.** Policy `CCallPolicy.NoHeap` and `CCallPolicy.noHeap_no_alloc_call`
  (`packages/backend-c/RumocaC/NoHeapPolicy.lean`); instances
  `CallPolicy.unit_no_heap`/`unit_acyclic`,
  `TensorCallPolicy.tensor_no_heap`/`tensor_acyclic`,
  `ConstantCallPolicy.constant_no_heap`/`constant_acyclic`, each carried as the
  `no_heap_acyclic` field of the three FMI source build contracts. Open:
  (a) numerical kernel bodies (`rumoca_rhs`, `rumoca_sample`, tensor helpers)
  are classified as leaves, not body-checked. M, proof. (b) Both eFMI
  Production Code call graphs have no policy instance. M, proof, after N01.
  (c) Allocation-free predicate over non-tree strings (preamble, storage and
  kernel strings), which also closes Rule 21.3 evidence. S-M, proof.
- **K02.7 RTOS-callable kernel. Partial.** Production Code methods take a
  caller `Model` record; FMI kernel functions are pure over supplied arrays.
  Remaining: state the stack/state/scratch requirement and bind it to the
  existing native boundary (`tests/efmi-tensor-native.c`,
  `tests/efmi-production.sh`). S, doc+native, after N01.

Exit evidence: K02.1-K02.7 closed; certified storage and call-graph policy in
every FMI and eFMI artifact contract; full gate.

## K03 - Complete public FMI execution and histories

Definition. Every emitted FMI 3 function has a mandatory actual-adapter
contract covering success, null, invalid-argument, lifecycle,
unsupported-capability, logging and return cases, and named ME and CS
refinement theorems relate every admitted host history, from creation
through initialization, operation, errors, reset and release, to the source
IVP under explicit host ownership rules. FMI 3.0.2 section 2.2.1 applies:
logger callbacks do not reenter the FMU and the host serializes calls on one
instance. Finite-arithmetic preservation, continuous-solution accuracy and
native execution remain separate claims.

- **K03.1 API inventory against metadata. Partial.** Scalar: done;
  `FMI3.adapter_public_contracts` joins `PublicAPI.Covered` and every
  `PublicAPI.Entry` contract (75/75, trust-ledger section 3.1). Tensor: 75
  families bound through `TensorAdapter.Contract`; `fmi3DoStep` lacks
  finite-arithmetic outcomes (trust ledger section 3.2, finding F1). Constant:
  per-function contracts without a joined coverage theorem. Remaining: the
  constant and tensor joined theorems in the form of
  `adapter_public_contracts`, and the tensor DoStep outcome field. M, proof.
- **K03.2 Scalar creation/initialization/ME/CS histories. Done** for the
  covered interactions: `CSProtocol.correct`, `CSProtocol.Contract.released`,
  `MEProtocol.correct`, recurring initialization protocols
  (`FMI3InitializationProtocol*.lean`), rejection/recovery and logging
  variants. Package gates recorded to 1,007 inputs; included in every later
  full gate.
- **K03.3 Remaining public interactions in created lifetimes. Scalar near done (2026-09-25 gate `682f88f`): `InstanceQuery` composes Float64 get/set, the empty accessors of the other types and Terminate into the ME/CS scripts; residue: empty-selection Clock/Interval/Shift and OutputDerivatives calls (adapter returns Error where OK is required) and multi-instance interleaving; tensor and constant open.**
  Access interleavings at later restarts and public calls outside the
  composed scripts (event indicators, nominals, time/entry calls interleaved
  with Float64 access in CS) are not composed. Tensor and constant have no
  lifetime histories beyond `TensorLifecycleHistory`. L (scalar) + L (tensor,
  constant), proof.
- **K03.4 ME/CS trace refinement. Scalar partial (2026-09-25): `MEProtocol.Lifetime`/`CSProtocol.Lifetime` bound as `CheckedFMI3Files.lifetimes`; tensor and constant open.** One theorem per interface from
  creation to release under explicit host ownership, including preservation of
  other instances and observable callback traces, for all three FMI products.
  Depends on K03.3 and K02.4. XL, proof.
- **K03.5 CS overflow outcomes. Open.** FMI CS Euler-update overflow
  (numerical-outcomes criterion 3) and tensor DoStep finite-arithmetic
  outcomes (F3): prove saturation/overflow behavior or state the excluded
  domain in the contract and [standards-review.md](standards-review.md). M-L,
  emitter+proof.

Exit evidence: named ME and CS refinement theorems for every admitted history
and emitted function of all three FMUs; full gate.

## K04 - Composed source, output and provenance contracts

Definition. One driver theorem, quantified over all admitted source texts,
contains every mandatory lower-stage contract and every public observation,
binds all published members to one source and one Solve product, and carries
complete provenance. A certificate for one member cannot close K04.

- **K04.1 Single driver theorem. Partial.** Existing components:
  `compiler_semantic_preservation`, `compile_verified`,
  `compiler_preserves_property` (`Verified.lean`, scalar C); the three FMI
  source build contracts; `EFMIArchiveProofs.archive_correct`,
  `compile_archive_verified`, `tensor_archive_correct`,
  `tensor_executed_archive_correct`. They are separate per product and profile.
  Remaining: one statement over the admitted source grammar that selects the
  profile, retains rejection, and contains the K03.4 refinement and K04.2-K04.4.
  L-XL, proof, after N01 and K03.4.
- **K04.2 Translation-unit interpretation. Partial.** Printer, literal pool,
  function table and linkage are bound to the actual bytes
  (`StaticRuntime.factory_definition`, `external_undefined`; C token grammar
  certificates). Remaining: header/macro meanings (`FMI3_FUNCTION_PREFIX`,
  `<math.h>`, `<fenv.h>`, `<stdatomic.h>`) as a stated interpretation, and
  object layout shared with K02.5. L, proof+native.
- **K04.3 Correlated members. Partial.** FMI: C, XML and capability metadata
  share the source (`CapabilityMetadata.ArtifactContract` in the source build
  contracts). eFMI: Algorithm Code, Production Code and manifests are bound per
  archive. Remaining: one correlation over value references, capability
  flags, manifest checksums and archive members for both targets, with
  fail-closed atomic publication stated in the contract. M-L, proof, eFMI half
  after N01.
- **K04.4 Provenance and source maps. Partial.** Located parsing and
  required origins exist ([provenance.md](provenance.md); required IR,
  GALEC/Algorithm and C initialization origins in
  [standards-review.md](standards-review.md)). Remaining: whole-file and
  archive source maps with original-to-staged identity and one origin per
  tensor operation. L, proof+emitter.

Exit evidence: one actual-source-to-artifact theorem containing every
mandatory lower-stage contract and provenance binding; existing artifact
rejection gate; full gate.

## K05 - Standards, MISRA and assurance review

Definition. The whole admitted subset is reviewed against MLS 3.7, FMI 3.0.2
ME/CS, eFMI 1.0.0 Beta 1 and MISRA C:2025 (user PDF, 223 guidelines: 22
Mandatory, 154 Required, 46 Advisory, Rule 15.5 Disapplied), with MISRA
Compliance:2020 and Appendix E documentation, a reviewed trust and quantifier
ledger, fresh-workspace reproduction and independent review. Mandatory
guidelines cannot be deviated. eFMI's MISRA AC AGC and C:2012 references are
mapped separately. No certification claim follows
([airborne-assurance.md](airborne-assurance.md)).

- **K05.1 Whole-subset standards findings. Open.** Open IDs: S01/SR08
  (initialization across the three standards), SR04, SR07, Startup
  input-initialization conflict, block-direction TODO, CF01-CF03, TF01-TF02,
  ES01-ES07 restricted interpretations, N01 (pending). Remaining: close or
  record each with its criterion in [standards-review.md](standards-review.md).
  L-XL, mixed.
- **K05.2 MISRA C:2025 matrix, 223 rows. Partial.** Ledger drafted; 0 rows
  Compliant, 215 Open. Gated repairs done: explicit null guards (Rule 11.11
  scope), `count != ((size_t)0)` (`build/count-condition-gate`), seedless
  `CTree.Expr.disjunction` (`build/fold-terminal-gate`),
  `CTree.Expr.nonfinite` (`build/misra-isfinite-gate`). Remaining, in order:
  - P0 category/title corrections (14 rows, including Rule 21.12 Required and
    violated by every adapter; Rules 7.5, 17.9, 18.10, 21.22, 22.12, 22.14,
    22.20 Mandatory) and stale evidence sentences. S, doc.
  - Feature-absence and allocation-free predicates on actual FMI bytes
    (Rules 12.2-23.8 structural set, 21.3). S-M, proof, no byte change.
  - Unused-code (2.3-2.8) and definite-initialization (9.1) predicates. M, proof.
  - Typed constants: floating 10.3/10.4 (19/20/20 sites), Boolean 10.3
    (13/11/11), `size_t` and value-reference 10.4 (56 and 4/7/4 per adapter),
    Rule 17.8 in `rumoca_sample`. Four M slices, emitter+proof.
  - Essential-type checker for 10.1-10.8, 14.4, 11.11 over `CTree`. L, proof.
  - After N01: unsigned counter constants, internal linkage and generated
    `production.h` (8.4, 8.7, 8.8, 2.1), Rule 2.2 dead store in Integrator
    Recalibrate, binary64 guard in tensor `model.c`/`production.c` (Dir 1.1,
    12.1), Dir 4.15 row. Four M slices, emitter+proof.
- **K05.3 Per-row record. Open.** Category, scope, independent predicate or
  analyzer/manual evidence, actual-file binding, finding or approved
  deviation, reviewer, for all 223 rows. Proposed dispositions: D1 Rule 10.1
  exact grid inequalities (`StepEntry.input_condition_all`,
  `StepGuards.grid_condition`), D2 Rule 21.12 read-only `fegetround`
  (`Runtime.stepRounding`), D3 Rule 11.5, D4 Rule 2.7 (FMI signatures), D5
  Rule 15.5. None approved. M, doc.
- **K05.4 Headers, interfaces, concurrency. Open.** Adopted FMI headers,
  compiler options, Dir 5.1-5.3 and Rule 21.25 for the atomic pool, native
  RTOS timing/stack/atomic assumptions. M-L, proof+doc.
- **K05.5 MISRA Compliance:2020 and Appendix E. Partial.** Section "Generator
  documentation" in [misra-c-2025.md](misra-c-2025.md) exists. Remaining:
  guideline enforcement plan, compliance summary, runtime failure policy,
  integration interface; MC08 AC AGC and C:2012 mapping for both
  `production.c` files. M, doc.
- **K05.6 Trust and quantifier ledger. Partial.**
  [trust-ledger.md](trust-ledger.md) classifies premises; open F3, F4
  (external bindings `floor`, `fegetround`, `atomic_exchange`, `atomic_store`,
  logger into the trust-boundary section of verification.md), F5 (C/IEEE
  boundary against a pinned toolchain), F7 (eFMI schema/XSD). Audited roots
  retain only `propext`, `Quot.sound`, `Classical.choice`. M, doc, final pass
  after all other items.
- **K05.7 Fresh-workspace reproduction and independent review. Open.**
  Reproduce the release from a clean checkout with normal Lake/mathlib
  artifacts; record source, grammar, toolchain, checker identity, roots and
  outputs; obtain independent reviewer sign-off on K05.2-K05.6; run the final
  full gate at that revision. M plus external reviewer time.

Exit evidence: resolved standards findings; complete MISRA enforcement matrix
and compliance summary; reviewed trust ledger; independent review; full gate
at the reproduced revision.

## Ordering

Lanes by file ownership. N01 owns `packages/galec-parser`, core GALEC
elaboration and `RumocaCore/Real`, backend-c `TensorProductPreflight*`,
`TensorFiniteScan*`, `Calls.lean`, backend-efmi `CInterface.lean` and
`Tensor*`, backend-fmi3 `TensorDerivativeDiscard.lean`, compiler `TensorEFMI*`,
`EFMITensor*`, `ArtifactCheck.lean`, `tests/efmi-*`, and the Dir 4.15 ledger row.

Parallel now (disjoint from N01 and from each other):

1. **Predicates (K02.6c, K05.2):** allocation-free and feature-absence
   predicates, then unused-code and definite-initialization. New backend-c
   module plus registration in `FMI3BuildArtifactCheck.lean`,
   `ConstantFMI3BuildArtifactCheck.lean`, `TensorFMI3BuildArtifactCheck.lean`.
   No byte change.
2. **FMI emitter lane (K02.3a, K05.2), serial:** reused-slot initialization
   first, then floating, Boolean, `size_t`/value-reference constants and Rule
   17.8. Backend-fmi3 factory/reset/runtime and compiler FMI adapter
   contracts; one gate per slice; frozen byte predictions per slice. Coordinate
   the artifact-check registration line with lane 1.
3. **Documentation (K02.1, K05.2 P0, K05.3, K05.5, K05.6 F4):** ledger
   corrections, deviation drafts, compliance summary, trust-boundary bindings.
   Draft now; merge `misra-c-2025.md` after N01's ledger edit.
4. **Scalar histories (K03.3 scalar, K03.4 scalar):** compiler
   `FMI3*Protocol*`, backend-fmi3 initialization-protocol modules; disjoint
   from lanes 1-3. Tensor/constant histories and K02.4 start after lane 2's
   factory change lands.

After N01: eFMI no-heap instance (K02.6b), RTOS statement (K02.7), eFMI
predicates, the four post-N01 MISRA slices, K04.3 eFMI half, MC08.

Critical path to "K02-K05 complete": N01 gate -> K02.3a -> K02.4 and K03.3
(tensor, constant) -> K03.4 ME/CS refinement (XL) -> K04.1 driver theorem ->
K05.6 final ledger pass -> K05.7 reproduction, independent review, final
gate. The MISRA chain (P0 -> predicates -> typed constants -> essential-type
checker -> post-N01 slices -> dispositions) runs beside it and must finish
before K05.7. Estimated remaining work: K02 about 6-8 gated slices, K03 about
10-14, K04 about 8-12, K05 about 14-18 plus external review; roughly 40-50
gated slices in total, of which the K03.4 -> K04.1 chain is the longest
serial dependency. Independent reviewer availability is the one external
dependency on the path.
