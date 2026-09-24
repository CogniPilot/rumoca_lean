import RumocaCore.Array.Solve
import RumocaCore.Solve.PointwiseProofs
import RumocaCore.GALEC.Elaboration.Square.Layout
import RumocaCore.GALEC.Elaboration.Scalar.Preparation
import GALECParser.Print

/-! Algorithm Code emission for the tensor square profile. The block is a source
tree assembled from the core builders: the square declarations, the Startup
initialization body, the empty Recalibrate method and the DoStep square body.
Loops keep rank and extents through `size` queries; no tensor cell is
enumerated. The text is `Print.block` of that tree. This file resolves no names,
solves no equations and selects no numerical policy; the prepared
`Solve.PointwiseIVP` kernel is the source of truth for the problem. -/
namespace Rumoca.EFMI
open Rumoca.Tensor Rumoca.Solve Rumoca.Solve.Tensor
open GALEC GALEC.Elaboration

/-- The prepared pointwise square kernel: zero initial state, the elementwise
product derivative and the diagonal Jacobian coefficient program, all universal
in the state shape. It is the kernel that `ArrayProfile.Solved.lower` computes
for the Jacobian body of the array profile. -/
def squareKernel (shape : Shape) : PointwiseIVP shape :=
  ⟨Solve.Tensor.fill shape .zero, ArrayProfile.squareProgram shape,
    some (ArrayProfile.squareJacobianProgram shape)⟩

/-- Admission token for the tensor Algorithm Code: it binds a rendered block to
the prepared square kernel of its shape, mirroring the scalar `GALEC.Model`
profile field. It does not license an arbitrary pointwise problem. -/
structure TensorModel (shape : Shape) where
  kernel : PointwiseIVP shape
  profile : kernel = squareKernel shape

/-- The Jacobian output's coefficient program evaluates to the forward-mode
tangent of the elementwise square in the unit input direction: the pointwise
product `u * one` added twice, i.e. the doubled input. This is the diagonal of
the pointwise Jacobian. -/
theorem square_jacobian_coefficients (shape : Shape) (ops : ScalarOps α) (zero one : α)
    (state input : Value α shape) :
    (ArrayProfile.squareJacobianProgram shape).coefficients.eval ops zero one
        (Env.push state (Env.push input Env.empty)) =
      BinaryOp.eval ops .add
        (BinaryOp.eval ops .mul input (Value.fill shape one))
        (BinaryOp.eval ops .mul input (Value.fill shape one)) := by
  simp only [ArrayProfile.squareJacobianProgram, Program.eval, Literal.eval]
  rw [Program.forward_correct]
  rfl

/-- Startup clears the state output `x` and the Jacobian output `J`, then sets
the sample period. -/
def squareStartup : AST.Method :=
  ⟨.ident "Startup", Initialization.Body.source "x" "J" "samplePeriod", .ident "Startup"⟩

/-- DoStep assigns the pointwise product `u[k] * u[k]` to `x`, clears `J` and
scatters the diagonal coefficients `u[k] + u[k]`. -/
def squareDoStep : AST.Method :=
  ⟨.ident "DoStep", Square.squareSource "u" "x" "J", .ident "DoStep"⟩

/-- The tensor square block for a state extent: input `u`, outputs `x` and `J`,
the protected sample period, and the Startup, Recalibrate and DoStep methods. -/
def squareBlock (extent : Nat) : AST.Block :=
  ⟨.ident "TensorSquare", Square.squarePublic extent, Square.squareProtected,
    [squareStartup, Scalar.recalibrateMethod, squareDoStep], .ident "TensorSquare"⟩

/-- The tensor Algorithm Code text of a prepared square model: the square block
at the state extent of the model's shape. -/
def renderTensorAlgorithm (_model : TensorModel ⟨[extent]⟩) : String :=
  Print.block (squareBlock extent)

/-- The state extent of the admitted array profile, read from its prepared shape. -/
def squareExtent : Nat := ArrayProfile.stateShape.dimensions.headD 0

/-- The admitted prepared square model. -/
def admittedModel : TensorModel ArrayProfile.stateShape := ⟨squareKernel _, rfl⟩

/-- The emitted tensor Algorithm Code text of the admitted model. -/
def tensorAlgorithmSource : String := renderTensorAlgorithm admittedModel

end Rumoca.EFMI
