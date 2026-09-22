import RumocaCore.Array.Solve
import RumocaCore.Solve.PointwiseProofs

/-! Algorithm Code rendering for the fixed-extent tensor square profile. The
derivative method is the elementwise product of the input with itself and the
Jacobian output is the prepared diagonal coefficient program. As in the scalar
profile the canonical names are fixed; this file resolves no names, solves no
equations and selects no numerical policy. The prepared `Solve.PointwiseIVP`
kernel is the source of truth, so a backend cannot invent a different problem. -/
namespace Rumoca.EFMI
open Rumoca.Tensor Rumoca.Solve Rumoca.Solve.Tensor

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

/-- The independent GALEC-level semantics of the tensor derivative method: the
input register and its elementwise product. Arithmetic is a parameter, exactly
as in the scalar expression semantics. -/
inductive TExpr (shape : Shape) where
  | input
  | mul (a b : TExpr shape)
  deriving Repr, DecidableEq

def TExpr.eval (ops : ScalarOps α) (input : Value α shape) : TExpr shape → Value α shape
  | .input => input
  | .mul a b => BinaryOp.eval ops .mul (a.eval ops input) (b.eval ops input)

/-- The derivative method body of the admitted profile. -/
def derivativeExpr (shape : Shape) : TExpr shape := .mul .input .input

/-- GALEC to Solve refinement of the derivative method: the GALEC semantics of
the elementwise product equals the prepared kernel's right-hand side, for every
rank, extent, arithmetic interpretation, state and input. -/
theorem square_derivative_refines (shape : Shape) (ops : ScalarOps α) (zero one : α)
    (state input : Value α shape) :
    (derivativeExpr shape).eval ops input =
      (squareKernel shape).problem.rhs ops zero one state input := rfl

/-- The Jacobian output's coefficient program evaluates to the forward-mode
tangent of the elementwise square in the unit input direction: `u .* one` twice
added, i.e. the doubled input. This is the diagonal of the pointwise Jacobian. -/
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

/-- Canonical Algorithm Code text of the admitted tensor square profile. The
declarations use the concrete extent-2 arrays of the profile; the derivative
method assigns the elementwise product and the Jacobian output applies the
authored `jacobian` extension to that product differentiated by the input.
GJ01's missing normative function definition/interface remains open. -/
def tensorUnitSource : String :=
  "block TensorSquare\n" ++
  "    input Real u[2];\n" ++
  "    output Real x[2];\n" ++
  "    output Real J[2, 2];\n" ++
  "protected\n" ++
  "    constant Real samplePeriod;\n" ++
  "public\n" ++
  "    method Startup\n    algorithm\n" ++
  "        self.x := 0.0;\n" ++
  "        self.samplePeriod := 1.0;\n" ++
  "    end Startup;\n" ++
  "    method Recalibrate\n    algorithm\n    end Recalibrate;\n" ++
  "    method DoStep\n    algorithm\n" ++
  "        self.x := self.u .* self.u;\n" ++
  "        self.J := jacobian(self.u .* self.u, self.u);\n" ++
  "    end DoStep;\n" ++
  "end TensorSquare;\n"

/-- The tensor Algorithm Code emitter. The admitted profile pins the text, so
this reads the prepared kernel only as provenance, mirroring the scalar emitter
whose block is likewise fixed by its profile. -/
def renderTensorAlgorithm (_m : TensorModel shape) : String := tensorUnitSource

theorem tensor_emission_is_unit (m : TensorModel shape) :
    renderTensorAlgorithm m = tensorUnitSource := rfl

end Rumoca.EFMI
