import RumocaEFMI.TensorProductionCode

/-! Refinement of the tensor square Production Code to the tensor Algorithm Code
semantics, and the certified numerical contract of the emitted translation unit.

The Production Code method functions call the prepared kernel entries rather than
re-emitting the numerical code. The numerical behavior is therefore the certified
kernel entries' behavior: the derivative entry `rumoca_rhs` computes the prepared
derivative program and the diagonal entry `rumoca_square_jacobian_diag` writes the
dense diagonal Jacobian `diag(2*u)`. Those storage and refinement facts are the
tensor C artifact contract, which this file bundles. The refinement theorems tie
the prepared kernel the Production Code computes to the tensor Algorithm Code's
denotation, universal in the state shape. -/
namespace Rumoca.EFMI.TensorProduction
open Rumoca.Tensor Rumoca.Solve Rumoca.Solve.Tensor
open Rumoca.CTensor.ProgramFixture

/-! ### The derivative method computes the prepared derivative

The DoStep method's derivative call supplies the readable input register `u` for
both the (unused) state register and the input register of the square right-hand
side. The prepared derivative the entry computes is therefore the elementwise
product `u .* u`, which is exactly the tensor Algorithm Code derivative method's
denotation. This holds for every rank, extent, arithmetic interpretation and
input, so no backend can substitute a different derivative. -/
theorem doStep_derivative_refines (shape : Shape) (ops : ScalarOps α) (zero one : α)
    (input : Value α shape) :
    (squareKernel shape).problem.rhs ops zero one input input =
      (derivativeExpr shape).eval ops input :=
  (square_derivative_refines shape ops zero one input input).symm

/-! ### The Jacobian output computes the diagonal Jacobian

The prepared Jacobian coefficient program the tensor Algorithm Code renders
evaluates, in the unit input direction, to the doubled input `u + u`; that vector
is the diagonal the scratch-free entry `rumoca_square_jacobian_diag` materializes.
The two coincide for every rank, extent, arithmetic interpretation and input. -/
theorem doStep_jacobian_refines (shape : Shape) (ops : ScalarOps α) (zero one : α)
    (input : Value α shape) :
    (ArrayProfile.squareJacobianProgram shape).coefficients.eval ops zero one
        (Env.push input (Env.push input Env.empty)) =
      BinaryOp.eval ops .add
        (BinaryOp.eval ops .mul input (Value.fill shape one))
        (BinaryOp.eval ops .mul input (Value.fill shape one)) :=
  square_jacobian_coefficients shape ops zero one input input

/-! ### The certified numerical contract of the emitted translation unit

The Production Code translation unit includes the certified kernel entries; their
tokenization, parse, finite IEEE execution and whole-tensor storage behavior is
the tensor C artifact contract. `IVPEntry.ArtifactContract` bundles the initial,
derivative and diagonal storage contracts together with the byte identity of the
certified sources. -/

/-- The Production Code product for the tensor square profile: the emitted
translation-unit bytes, the certified kernel contract they carry, and the
refinement of the derivative and Jacobian methods to the tensor Algorithm Code
semantics, universal in the state shape. -/
structure Contract (productionC : String) : Prop where
  /-- The actual Production C bytes are exactly the emitted translation unit. -/
  bytes : productionC = render
  /-- The certified kernel entries (initial, derivative, diagonal) carry their
  tokenization, execution and storage contracts and their source byte identity. -/
  kernel : IVPEntry.ArtifactContract IVPEntry.sources IVPEntry.jacobianDiagSource
  /-- The derivative method computes the prepared derivative `u .* u`, which is
  the tensor Algorithm Code derivative method's denotation, for every shape. -/
  derivative : ∀ (shape : Shape) {α} (ops : ScalarOps α) (zero one : α) (input : Value α shape),
    (squareKernel shape).problem.rhs ops zero one input input = (derivativeExpr shape).eval ops input
  /-- The Jacobian output computes the doubled input `u + u`, the diagonal the
  scratch-free Jacobian entry materializes, for every shape. -/
  jacobian : ∀ (shape : Shape) {α} (ops : ScalarOps α) (zero one : α) (input : Value α shape),
    (ArrayProfile.squareJacobianProgram shape).coefficients.eval ops zero one
        (Env.push input (Env.push input Env.empty)) =
      BinaryOp.eval ops .add
        (BinaryOp.eval ops .mul input (Value.fill shape one))
        (BinaryOp.eval ops .mul input (Value.fill shape one))

/-- The emitted tensor Production Code satisfies its contract: the byte identity
holds by construction, the certified kernel contract is discharged by the tensor
C artifact check, and the derivative/Jacobian refinements hold universally in the
state shape. -/
theorem production_correct (productionC : String) (printed : productionC = render) :
    Contract productionC :=
  ⟨printed,
    IVPEntry.artifact_correct IVPEntry.sources IVPEntry.jacobianDiagSource rfl rfl,
    fun shape _ ops zero one input => doStep_derivative_refines shape ops zero one input,
    fun shape _ ops zero one input => doStep_jacobian_refines shape ops zero one input⟩

end Rumoca.EFMI.TensorProduction
