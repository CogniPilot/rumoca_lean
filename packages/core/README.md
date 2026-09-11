# Rumoca core IR package

Target-independent Flat, DAE and Solve representations, finite Solve execution,
binary64 specifications and generic transition/behavior proofs. This package
does not import the compiler driver or any backend.

Use `lake build check-core` from the repository root for incremental core proofs and
axiom checks. `Tests/CoreAudit.lean`, `Tests/TensorChecks.lean` and `Tests/FiniteChecks.lean` belong to the
`RumocaCoreChecks` library, also selected by this package's `lake test`. See
[development commands](../../docs/development.md).

| Module | Contents |
| --- | --- |
| `RumocaCore`, `RumocaCore.IR.Flat`, `IR.DAE`, `IR.Solve` | Scalar IR types and lowering functions with required occurrence origins and initialization data |
| `RumocaCore.Provenance.Source`, `Provenance.Lowering` | Checked input context, closed transformation rules and source ancestry through the scalar chain |
| `RumocaCore.Initialization.Scalar`, `Initialization.Real`, `Initialization.Diagnostics` | Computable initialization selection, source/uniqueness proofs and exact declaration-based notices |
| `RumocaCore.Tensor` | Shared rank/extent types and shape-preserving array-backed storage |
| `RumocaCore.Tensor.Matrix` | Proved equivalence to mathlib matrices using mathlib's finite product indexing |
| `RumocaCore.Tensor.Operators` | Dense-array pointwise addition/multiplication and forward/reverse rules with explicit scalar arithmetic |
| `RumocaCore.Tensor.Differentiation` | Mathlib derivative, adjoint and shared-input square/Jacobian proofs for arbitrary shapes |
| `RumocaCore.Array.Builtin` | Parsed Jacobian semantics, uniqueness and correctness of the resolved square call |
| `RumocaCore.Array.IR`, `Array.Semantics`, `Array.Solve`, `Array.Lowering` | Array source/Flat/DAE equations, checked residual solving and composed executable IVP/Jacobian preservation |
| `RumocaCore.Array.Finite` | Actual square/AD program execution and nearest-value bounds against the Real RHS/Jacobian |
| `RumocaCore.Solve.Tensor`, `Solve.IVP` | Compact tensor programs, independent denotation, executable evaluator and explicit IVP |
| `RumocaCore.Solve.Tensor.Forward`, `Solve.Tensor.Differentiation` | Ordinary Solve-to-Solve forward AD, primal preservation, instruction bound and whole-program mathlib derivative theorem |
| `RumocaCore.Solve.Tensor.Reverse`, `Solve.Tensor.ReverseProofs` | Saved-primal reverse execution with cotangent accumulation and the adjoint/derivative contract |
| `RumocaCore.Solve.Tensor.Diagonal`, `Solve.Pointwise`, `Solve.PointwiseProofs` | Prepared IVP and dense diagonal observation using mathlib matrices, with execution contracts |
| `RumocaCore.Solve.Tensor.Finite` | Independent ordered finite execution, all-intermediate domain characterization and unique evaluator result |
| `RumocaCore.Solve.ModelData` | One executable root paired with typed declaration identities and names |
| `RumocaCore.Solve.Tensor.Origins`, `Solve.IVPOrigins`, `Solve.FMI3OriginProofs` | Required unit FMI operation origins and a composed value/source/actual-annotation preparation contract |
| `RumocaCore.GALEC.IR`, `GALEC.Semantics`, `GALEC.UnitProfile` | Checked unit Algorithm Code product of DAE, explicit state/clock initialization and independent method semantics |
| `RumocaCore.GALEC.Origins`, `GALEC.UnitOrigins`, `GALEC.OriginProofs` | Required operation/operand/method origins, independent rule/parent requirements and source ancestry |
| `RumocaCore.Solve.Algorithm`, `AlgorithmOrigins`, `AlgorithmOriginProofs` | Tensor register refinement of GALEC with required traces and composed value/origin preservation |
| `RumocaCore.GALEC.Protocol` | Restricted eFMI lifecycle reference and complete permitted-trace refinement |
| `RumocaCore.Driven.IR`, `Driven.Lowering` | Draft driven profile's Flat/DAE/Solve equations, initialization and per-pass proofs |
| `RumocaCore.Pass` | Generic behavior-preservation composition and property transfer |
| `RumocaCore.SolveSemantics` | Interpretation of Solve using the admitted finite sampling policy |
| `RumocaCore.Solve.ModelExchange` | Shared model state/derivatives, unit solver and nested CS state; internal contracts, not an FMI ABI |
| `RumocaCore.Real.Binary64`, `Real.Encoding` | Arithmetic specification, rounding proofs and finite bit encodings |
| `RumocaCore.Real.ScaledRounding`, `Real.Multiplication`, `Real.Addition` | Exact rational-input nearest/even rounding, finite product/zero-sign contract and Real error bounds |
| `RumocaCore.Real.Comparison` | Binary64 classification and ordered/unordered comparisons, with finite comparison-to-real-order proofs |
| `RumocaCore.FMI3.Time` | Independent ME time-history window and its lower-bound representation contract |
| `RumocaCore.FMI3.Initialization` | Independent finite initialization admission profile, optional argument bits and mathematical order connection |
| `RumocaCore.Transition` | Generic transitions, termination and observable behaviors |
| `RumocaCore.Profile` | Target-independent calls and relational unit-step policy; transport through equation equivalence |

The base runtime IR imports the parser's AST and its Std dependencies.
Dense matrix observations reuse mathlib's matrix definitions and finite
indexing; analytic proof modules add the derivative theory separately. Declarations keep their
`Rumoca` namespaces. Solve remains source indexed and carries its lowering
evidence; no C syntax or target function enumeration appears in these IR types.

```sh
# In nix develop, from the repository root:
lake build rumoca_core/RumocaCore

# Package-only build with its own pinned dependency manifest:
lake -d packages/core build
```

The [compiler package](../compiler/README.md) owns source semantics and the
end-to-end composition with parsing and output artifacts. Each backend consumes
Solve IR from this package and owns its target syntax, rendering and execution
contracts.

The eFMI branch is DAE → checked GALEC → Solve algorithm. Algorithm Code
rendering consumes the GALEC product; Production C must consume its Solve
refinement. This branch does not reconstruct DAE from GALEC or replace the
numerical IVP root. The [eFMI roadmap](../../dev/efmi.md) records the remaining
target, lifecycle-memory and actual-archive obligations.

The tensor IVP is the direction for the new input/state profile. The older
unit-only `Solve.Model` remains the production regression path until the new
path has a target execution and actual-artifact theorem. Neither the new tensor
types nor their mathlib bridge add Modelica arrays, matrix multiplication,
PDEs or neural ODEs to the compiler. See [the IR review](../../dev/ir-review.md).

The [tensor AD increment](../../dev/tensor-ad.md) has checked primitive rules
for mathematical Real tensors, including cotangent accumulation for `x .* x`.
`Array.Builtin` now connects the resolved source call to an independently
specified Fréchet derivative, with uniqueness of the resulting matrix.
`Solve.Tensor.Program` now includes whole-tensor arithmetic and a proved
forward transformation. Its reverse evaluator saves the primal intermediates
and accumulates contributions at shared references. Both have whole-program
contracts against the same mathlib derivative, beyond the primitive rules.
The array source-to-Solve chain now preserves the complete equations and fixed
initialization. Its explicit square Jacobian uses the forward transformation
and a diagonal materializer; the program has eight nodes independent of tensor
extents. Finite execution of these actual square and coefficient programs now
has nearest-value bounds against the Real RHS and derivative. Static reverse
lowering, C tensor loops and the FMI target edge remain open. These analytic
proofs do not differentiate IEEE rounding.

For arithmetic-only iteration, use `lake build rumoca_core/Tests.FiniteChecks`.
Array source corollaries remain in `Tests.TensorChecks`; unrelated core and
lifecycle audit roots keep their native Lake cache entries.
