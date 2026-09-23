# Resume handoff — 2026-09-23 UTC

## Subsequent resumption — generic owner adoption

The goal was reactivated after the wrap-up below; main verified its active
status and resumed from clean `f6eb14c`. Five modules are now integrated:
`Elaboration.Block.{Headers,Preparation}`, `Methods.{Correspondence,Sequence}`,
and `Layout.State`, with five audit leaves/61 roots. They preserve the reviewed
scratch statements while moving metadata/execution correspondence out of the
restricted block profile. Owner session40817 passed `check-core` (2,433 jobs).
The concrete Square/Source and fresh-parser/C/artifact cutover remain scratch.
Required full gate and post-audit use `build/layout-state-*`; inspect their
actual terminal files/handles before resuming or restarting anything.
This section supersedes the paused/live-status and first-next-action statements
below; the remaining cutover map and baseline evidence still apply.

## Start here

The user requested a wrap-up and handoff, not more implementation. Resume only
when asked. This file supersedes the next-action/session instructions in
`dev/account-handoff.md` and older ignored checkpoints. The overall compiler
goal is **not complete**; do not mark the persistent goal achieved.

Workspace: `/home/jgoppert/git/rumoca_lean`, branch `main`.
Baseline HEAD and last verified pushed revision: `92ad9f0`.
`ba091c6` is the latest implementation covered by the required full gate;
`92ad9f0` records that gate in three documentation ledgers.
The subsequent handoff commit is documentation only. Check `git status` and
`git log` on arrival rather than assuming the baseline is still HEAD.

Important: the new proof work and its dependencies are under ignored `build/`.
They remain in this workspace, **not in Git**. An account switch on this same
machine retains them; a fresh clone does not. Preserve the existing `build/`
tree if moving machines. Do not mistake scratch checks for production adoption.

## Non-negotiable working constraints

- Read `AGENTS.md`, `docs/verification.md`, `docs/layout.md`, and the current
  stage entries in `dev/standards-review.md` before semantic changes.
- Compiler, grammars/tooling, semantics and proofs are Lean. Both production
  frontends use the reusable in-tree LALR engine; no token/body recognizers.
- Spiral development: persistent core mechanisms, not temporary architecture.
  Tensor rank/extents/operations stay in indexed IR; no lowering-time cell
  enumeration. Ordinary source expansion is blocked by open standards findings;
  the user authorized repair of the already admitted cases.
- New production acceptance requires original source semantics, lowering,
  target execution and the actual-artifact contract together. Never weaken
  existing contracts/audits, introduce `sorry`/`admit`/axioms, or use native proof
  reduction. Keep machine compilation/ABI/native testing outside the proved C
  boundary unless separately established.
- Solve owns executable IVP; shared C emission belongs to `backend-c`;
  FMI/eFMI wrap prepared Solve and must not redo source resolution/lowering.
- Required gate: `nix develop .#verification --command lake test`.
  Package checks or scratch axiom audits are not substitutes.
- User prefers Astra agents, bounded parallel tasks and adversarial review,
  with low token burn. Reuse checks/dependencies; avoid repeated full gates for
  unchanged inputs. Commit often using James Goppert
  `<james.goppert@gmail.com>`, `-s`, **no AI co-author**. Push only as authorized.

## Verified production baseline — already finished

Core owns `GALEC/Elaboration/Scalar/{Preparation,Execution,State,FiniteArithmetic}`.
For every resolved old scalar block, generic named preparation retains its
actual declarations, names and bodies. Independent source execution is exact
for Startup/Recalibrate/literal-one DoStep; whole-shaped state/clock adapters
have two-sided inverses. Only the actual finite addition-with-one domain is
discharged, not arbitrary arithmetic totality.

Backend `RumocaEFMI/ScalarSourceProofs.lean` supplies `ScalarSourceSemantics`.
Compiler `AlgorithmContract.original_source` makes it mandatory for the actual
parsed member, carried by Production/Manifest/Archive contracts.
`ProductionContract.original_methods` composes source execution with authored
C behavior at the same final state and complete heap frame. The existing
allocated-only Startup branch remains. No production parser/emitter changed.

Full gate session **67522** and post-audit **66369** both finished **exit 0**.
Do not restart or poll these completed sessions. Evidence prefix:
`build/scalar-source-`:

- `full-gate-v1.{log,exit,axioms}` and `post-audit-v1.{log,exit}`;
- 2,654 frozen input hashes, 8,719 complete unchanged-whitelist audit reports;
- all 573 selected roots and four retained actual FMU roots;
- three FMI matrices, 75 functions each, 526/650/526 behavior cells, zero
  discrepancies/unexpected results;
- scalar/tensor Algorithm and Production members byte-identical.

The frozen manifest includes ledgers subsequently updated in `92ad9f0`;
historical manifest mismatch against later documentation is not a new code
failure. No full gate is currently running.

## Latest unowned work — whole-shaped method handoff

Directory: `build/galec-layout-state-draft/`.
Namespace: `Rumoca.GALEC.Elaboration.LayoutStateDraft`.

1. `LayoutStateDraft/Partition.lean`: existing `Env`/`Value` representation,
   structural traversal of declarations, read-only/writable projections and
   join; two-sided roundtrips, injectivity, metadata-aligned repartition,
   preservation, identity, composition, inverse and uniqueness. Alignment
   requires **full ordered descriptors**, not merely equal shapes or names.
   Roles can change; no policy permission is inferred.
2. `Methods.lean`: `prepared_sequence` fixes two selected original methods from
   the same block before all runtime values/arithmetic. Source execution of the
   pair is iff prepared IR execution, using the **actual first post-store** for
   transfer. Final read-only values are included, not just output observations.
   `prepared_handoff` characterizes whole-state preservation without itself
   asserting execution. Reuses `BlockPreparationDraft.prepared_metadata_eq`.
3. `Square.lean`, namespace `SquareTransfer`: arbitrary extent/whole values;
   Startup→later layout transfers `u`, `x`, `J`, and period exactly. After
   initialization, `u` is unchanged, `x/J` are filled with zero, and period is
   filled with one. `source_transfer_total` constructs source execution and
   this exact handoff for every old store/input and partial arithmetic
   interpretation, under existing positive/bounded source extents.
4. `Source.lean`: `parsed_startup_handoff` binds the actual repaired 266-token
   source witness, whole-block preparation and selected original Startup
   **before** all runtime choices, then constructs execution and the initialized
   later-method pair. It has no caller-supplied source-execution premise.
5. `Audit.lean`: 31 explicit roots, unchanged foundation whitelist.

These proofs do not establish C heap representation across calls, sequential
public C lifecycle, normative input initialization, production parser cutover,
emitted-byte equality or actual archive contracts. Zero-sized generic layout
theorems do not admit zero-sized source arrays.

Final check **session65410 completed exit 0**: 31 roots, four empty
implementation logs, seven local source/script hashes, 30 selected input hashes,
five output hashes and four retained upstream source manifests. The unchanged
whitelist passed. This is a scratch receipt, not a new production full gate.
Final receipt: `final-v1.exit` and `check-final-v1.exit`; logs
`{Partition,Methods,Square,Source,Audit}-final-v1.log`; frozen
`final-v1-{sources,inputs,outputs}.sha256`, upstream-hash and whitelist logs,
and `final-v1.axioms`. The four implementation logs must be empty and all
31 roots present. Read the terminal receipt before relying on it.
Check command, with a **new** version label if rerunning:

```sh
nix develop .#verification --command lake env bash \
  build/galec-layout-state-draft/final-check.sh final-v2
```

Independent review: `independent-review.md`; worker scope/check notes:
`square-review.md`; main review/receipt: `README.md` in the same directory.
Earlier V1/V3/V5/V7 failures were local elaboration failures, retained as such;
V6 partition, V8 methods and V10 square/source/audit all passed. Do not use
old V4 as evidence for later composition additions.

## What to do next — production repair, not more unrelated features

Read `build/galec-production-cutover-review.md` completely. Its replacement map
is useful, but its missing scalar-preservation and total-Startup findings are
historical: those prerequisites now exist. In priority order:

1. Integrate the reviewed generic block preparation and whole-shaped handoff
   mechanisms into appropriate core ownership. Extract metadata equality to
   the generic method owner; avoid importing concrete fixtures or `build/`
   modules. Register all proof roots. Keep original-body execution and complete
   state semantics, not just successful preparation.
2. Complete the fresh GALEC parser/action/source cutover, preserving every old
   scalar source/product via the existing universal compatibility proof.
   Extract generic source provenance from its concrete certificate imports.
   Preserve or explicitly prove/adapt diagnostics; do not retain a production
   old-profile fallback. The tensor GALEC bytes must change together with the
   emitter; preserving obsolete `.*`/undeclared-call syntax is not the goal.
3. Adopt the repaired tensor Algorithm source and actual C Startup together
   with their contracts. Startup must clear **both x and J** and set period;
   current production preserves arbitrary old J and is wrong for this repair.
   Replace that old outcome/frame, not conjoin contradictory clauses. Update
   existing `tests/efmi-tensor-native.c` Startup/first-Recalibrate expectations;
   retain subsequent Recalibrate, input, guard/status and DoStep checks.
4. Bind original-body semantics, prepared kernel/AD, actual public C table,
   both actual grammar/source members, rendered C, XML/checksums and ZIP in the
   production artifact chain. Compose input/heap representation and lifecycle
   where needed; the new logical transfer alone does not prove that boundary.
5. Review, package-check and run the required full artifact gate before claims
   or any further source expansion. Keep FMI retained roots and existing
   scalar/tensor/constant-rate products. No new backend/plugin is needed.

Useful completed scratch (read their READMEs/reviews, do not regenerate blindly):

- `galec-startup-parser-draft`: statement-list/indexed/loop LALR instance,
  21 rules, 598 canonical/178 LALR states, 44 audited roots.
- `galec-scalar-scanner-draft`: six universal scanner roots.
- `galec-scalar-parser-compat-draft`: 21 roots, every old successful scalar
  source parses to its exact fresh AST embedding; not diagnostic equivalence.
- `galec-scalar-preparation-draft`: 62-root combined scratch receipt; most
  modules already owned, fresh-parser source composition remains unowned.
- `galec-block-preparation-draft`: 55 roots, original three methods from one
  actual source; source provenance currently imports concrete fixtures.
- `galec-startup-certificate-draft`: actual 266-token source, 25 Startup roots
  and eight DoStep roots; DoStep remains square RHS/Jacobian, not Euler.
- `galec-startup-{c,link,public,public-link,total}-draft`: reviewed candidate
  repaired C/public Startup chain. Total theorem removes the source-execution
  premise but does not promote candidate tables to actual artifacts.

## Standards and claims that must remain open

Pinned MLS 3.7, FMI 3.0.2 and eFMI 1 Beta1. Whole-subset standards review precedes
ordinary grammar expansion. Carry GJ01/GJ03, N01, S01/SR08, input initialization,
native/lifecycle and MISRA findings forward until their actual obligations close.
No safety-critical readiness, CompCert-equivalent coverage or MISRA conformance
claim is justified. User's MISRA PDF is under `/home/jgoppert/Documents`.

Important corrected finding: eFMI Beta1 §3.1.6 **permits scalar-encoded uniform
array starts**. Current manifest `start="0"` is not a cardinality defect.
Do not introduce element serialization to “fix” it. This permission does not
license scalar-to-array GALEC assignments or solve Startup input policy.
The pinned Startup input-initialization versus forbidden-input-write conflict
remains; do not invent an integration agreement or broaden input writability.

The bounded review agent was collected and closed at wrap-up. No new full gate
or implementation task is left running. On resumption, inspect
current sessions/processes if evidence is ambiguous; a timeout is not termination.
