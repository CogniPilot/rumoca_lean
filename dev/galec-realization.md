# Bounded tensor realization prerequisites — 2026-09-22

## Typed loop bodies and prepared square composition — full gate passed

The concrete typed pointwise, nested rectangular-clear, diagonal-scatter and
whole square/Jacobian bodies now instantiate the reusable statement semantics.
They are parameterized by extents, typed input/output references, iterator
contexts and arbitrary initial stores. Loop bodies are constructed once, not
per tensor element. The pointwise/coefficient templates are explicitly rank
one; clearing is rectangular rank two. No all-rank renderer is claimed.

`StoreIteration` lifts arbitrary partial/nondeterministic tensor executions to
the existing typed environment, with a sufficient and necessary whole-store
frame. `CoefficientTerms` reifies the certified immutable expression into
ordinary reads/operators without AD or arithmetic rewrites. `MatrixClear`
proves exact row/nested prefixes and all-cell clearing; `MatrixBodies` connects
the literal-only nested body to it without assuming scalar arithmetic total.
`VectorBodies` proves exact finite execution of pointwise and scatter bodies;
`VectorDiagonal` composes clearing/scattering, retaining every expression domain.

`SquareBodies.body_executes` is an iff between the actual typed body execution
and the original prepared square RHS finite execution plus the exact final
two-update store. Existing `square_from_finite_rhs` supplies coefficient domains:
the primal multiplication is not dropped merely because doubling is finite.
`jacobian_value_prepared` relates each matrix coordinate to the actual
AD-generated `DiagonalProgram.eval`, with a proved vector-coordinate bridge.
`body_outputs` retains the finite RHS, prepared matrix and every unrelated
binding. Vector and matrix destinations are distinct by rank, even at equal
volume. Output equality is exact Binary64.Value equality, including signed zero;
off-diagonal clearing uses positive zero. Evaluator equality alone is explicitly
not a successful-execution or signal-handling claim.

The old public `scatter_prefix` statement is unchanged: its induction proof is
factored into the more general `scatterWith_prefix`, and the old theorem is a
wrapper. Existing `scatter` execution remains definitionally the same. One
dependent proof needs explicit beta reduction; no theorem or contract is weakened.
Generic bound reindexing changes only a proved-equal Fin bound, not tensor shape.

Owner V1 passed `lake build check-core` (2,312 jobs): 584 complete whitelisted
reports, all 62 new roots plus all 44 preceding typed-statement roots, no
new-module warnings. Independent Astra review found no semantic/adoption issue
and reconciled the 62 new roots. The matrix-clear sidecar's 15 roots were checked
and reviewed before adoption; main added independent loop-relation consequences.
Evidence: `build/galec-typed-bodies-owner-v1.*`,
`build/galec-typed-bodies-{new,required}-roots.txt`, and
`build/galec-matrix-clear-draft/`. Earlier failed elaboration logs remain separate.

Implementation `a7b854a`, including the `c9843b1` statement addition, passed
the required full gate V1/session92788 and post-audit V1/session52530, both
terminal exit 0. All 2,545 frozen inputs are unchanged; 8,184 complete reports
pass the unchanged whitelist; all 106 required roots and four retained FMU
roots are present. Three FMI matrices cover 75 functions each and 526/650/526
behavior cells, with no discrepancies/unexpected results. Existing actual-file,
native and mutation boundaries pass. Actual scalar/tensor Algorithm Code and
Production C members are byte-identical to baseline. Evidence:
`build/galec-typed-bodies-full-gate-v1.*`, `-post-audit-v1.*`,
`build/galec-typed-bodies-{before,after}-members.sha256`,
`build/galec-typed-bodies-fmu-retained-v1.axioms` and `-archives-v1.sha256`.
No grammar, emitter, production source
case or actual-artifact contract has changed. Parsed/elaborated GALEC linkage,
surface/target Integer bounds, signal/failure-state behavior, native aliasing
and repaired artifact evidence remain open. Adopt the prepared recurring review
before grammar edits, then connect these typed bodies through LALR actions,
elaboration, rendering, target refinement and actual-file/archive contracts.
GJ01/GJ03/N01 and all retained standards/MISRA findings remain open.

## Typed statement integration — owner passed; full repair gate pending

The next core prerequisite adds four modules, without grammar, source
admission, emitter or artifact-contract changes:

- `Tensor.Coordinates`: arbitrary-rank coordinates, a row-major dense-index
  equivalence, exact agreement with the existing vector/matrix layouts,
  one-based bounds and an exact checked one-based decoder round trip.
- `Solve.Tensor.Environment`: updates of the existing typed `Env`, with exact
  addressed reads and an independent frame iff for every other reference,
  including different nominal shapes. There is no new untyped register map
  or Solve-to-GALEC dependency.
- `GALEC.IndexSyntax`: intrinsically bounded iterator references and per-axis
  subscripts, with weakening/capture-preservation proofs even when nested
  binders have equal extents. Names are absent from this resolved core syntax.
- `GALEC.Statements`: typed scalar reads, output-only indexed writes,
  sequencing and bounded nested loops. Independent scalar/write/frame/loop
  relations compose to `Statement.execute_correct`, universal in syntax,
  contexts, arithmetic, iterator environments and initial/final states.

The evaluator theorem explicitly assumes total deterministic scalar arithmetic.
The independent execution relation permits partial/nondeterministic arithmetic;
it is not a proof that finite IEEE execution always succeeds. Future finite
execution with mutable output reads needs intermediate-state domain reasoning.
Inputs and iterators are separate immutable semantic environments; native
aliasing and parsed-source mutability still need their translation proofs.
Prepared Nat bounds do not prove target Integer representability or surface
range semantics. Zero-volume mathematics does not admit zero-sized GALEC arrays.
No callback or enumerated scalar instruction list is stored in the statement IR.

Scratch checks passed before adoption, including 44 complete whitelisted roots.
Integrated owner V1 passed `lake build check-core` (2,298 jobs): 522 complete
whitelisted reports, all 44 new roots, no new-module warnings. Independent
Astra semantic and adoption reviews found no issue after correcting ownership:
Environment imports Solve directly, while Statements imports TensorWrites.
All four audit modules are wired into the existing CoreAudit aggregator.
Evidence: `build/galec-statements-owner-v1.*`,
`build/galec-statements-required-roots.txt`, and scratch `build/galec-index-draft/`.

The full gate recorded below covers `8f9034b`, NOT these newer modules.
Next instantiate the pointwise and nested matrix-clear/diagonal-scatter bodies
in this typed syntax and connect their execution to the previously proved
realizations. Then complete the parser/elaboration/render/actual-artifact chain
under the reviewed repair scope. The prospective whole-subset checklist in
`build/galec-loop-stage-review-draft.md` was read by main, but still needs
adoption into the recurring ledger before any grammar edit. GJ01/GJ03/N01 and
all retained conformance/native/MISRA findings remain open.

## Gated bounded-execution and coefficient baseline

This is core semantic preparation for GJ01/GJ03, not a grammar cutover or a
new admitted source case. The production parser, emitted GALEC/C and artifact
contracts are unchanged. GJ01/GJ03/N01 and the other standards findings remain
open. In particular, existing artifacts still contain the unresolved GALEC
`jacobian` call and pointwise `.*` spelling.

## Reusable mechanisms

`RumocaCore.GALEC.BoundedIteration` defines structurally bounded ascending
execution and a separate inductive execution relation. Universal prefix/full
correspondence covers total deterministic bodies; guarded correspondence also
retains every index-dependent partial-arithmetic condition. Prefix invariants,
observation frames and one-based mathematical bounds are proved. No evaluator
fuel, opaque-callback IR or compiled list of scalar instructions is introduced.
The body argument is a semantic interpretation, to be supplied by a future
typed statement interpreter. State-dependent guards, errors and early exits
are not silently included in the guarded theorem.

`TensorWrites` proves independent indexed-assignment correspondence, prefix
and untouched-cell properties, complete pointwise overwrites, and matrix
zero-fill followed by diagonal scatter. Results are independent of arbitrary
old destination contents. `diagonal_prepared` relates the result to the
existing `Solve.Tensor.DiagonalProgram` for all shapes, arithmetic and typed
environments. It materializes prepared coefficients; it does not synthesize AD.

`CoefficientRealization` separates exact evaluator equality from successful
ordered finite execution. Its scalar expressions refer to an immutable input;
the pointwise interpretation retains the full nominal tensor shape. Independent
rounding relations supply expression execution, then indexed writes. Generic
pointwise and two-phase diagonal execution theorems connect these relations to
the tensor results. A `FiniteRealization` explicitly retains conditions from
ordered source instructions omitted by a compact expression. Its final
`materializes_iff` preserves both the original program domain and exact result.

`SquareRealization` reuses the existing source-owned square/AD proofs. It
instantiates pointwise scalar multiplication for the prepared RHS, and scalar
`u + u` for prepared Jacobian coefficients. It does not recompute AD or assume
an algebraic identity for arbitrary arithmetic. The finite bridge preserves
exact encodings, including negative zero, and retains primal-square finiteness
as well as finite coefficient additions. Execution of the original square RHS
supplies these conditions; they are not extra caller assumptions. The matrix
clear uses positive zero, independently of the coefficient's sign.

## Boundaries

All shapes, including zero volume and rank-zero volume one, are covered by
the semantic statements. That does not license GALEC zero-sized declarations,
an unchecked `1:0` range, or a flattened higher-rank surface index. Every value
and result retains rank and extents. Iterating cells is semantic runtime
execution, not compiler-lowering enumeration.

These modules do not establish mutable input/output nonaliasing, machine
Integer representability, surface one-based index conversion, GALEC loop-nest
syntax, parser/action completeness, signal/overflow policy, native floating
environment correspondence, or actual-file certificates for repaired output.
The recursive semantic evaluator is not a host stack/resource guarantee.
Finite arithmetic is a partial specification, not a claim that ordinary
GALEC arithmetic automatically signals or aborts on overflow.

Next: introduce reusable typed loop/index syntax with its elaboration and
execution proofs; connect it to these realizations, the existing prepared
Solve/C refinement and the actual-artifact chain. Review the entire admitted
subset before any repair grammar change. No backend name/shape inference or
AD, hardcoded parser path, contract weakening or new admission is authorized
by this prerequisite checkpoint.

## Evidence status

Core owner V5 passed (`lake build check-core`, 2,290 jobs): 478 complete axiom
reports passed the unchanged whitelist, with all 66 new declaration roots
present and no new-module warnings. All authored declarations have per-module
audit roots wired into `Tests.CoreAudit`; no old roots are removed. V1/V2/V4
retain elaboration failures; V3 passed the initial diagonal bridge before the
pointwise addition. The final owner log is `build/galec-realization-owner-v5.log`.

Independent Astra review found no issue in the iteration/write mechanisms or
the final finite/pointwise/diagonal composition. It explicitly retained the
limits above, including no failure-state/trace equivalence or executed
preflight guarantee. The reviewer did not duplicate the main owner's builds.
The required full artifact gate subsequently passed for implementation
`8f9034b`: `nix develop .#verification --command lake test`, V1 exit0. The
post-audit also passed: 2,523 frozen inputs unchanged, 8,078 complete reports
under the unchanged whitelist, all 66 new roots present, four retained FMU
roots separately audited. The three FMI matrices exercised 75 functions each
and 526/650/526 cells, with no recorded-finding discrepancies or unexpected
results. Existing parser/LSP/source/C/helper/FMI/eFMI artifact, mutation and
native boundaries passed. Actual scalar/tensor Algorithm Code and Production
C members are byte-identical to the baseline; this gate does not repair their
still-open GJ01/GJ03 output findings.

Evidence: `build/galec-realization-full-gate-v1.*`,
`build/galec-realization-post-audit-v1.*`,
`build/galec-realization-{before,after}-members.sha256`,
`build/galec-realization-fmu-retained-v1.axioms` and
`build/galec-realization-archives-v1.sha256`. Gate21657 and post98157 are
terminal exit0. No future typed-statement or renderer change is covered by
this frozen implementation's gate.
