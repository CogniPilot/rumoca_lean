# Bounded tensor realization prerequisites — 2026-09-22

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
The required full artifact gate is pending. A package check alone is not the
C/artifact gate.
