import RumocaCore.Solve.Pointwise
import RumocaCore.Tensor.Differentiation

/-! Mathematical execution conditions of the prepared pointwise IVP. These
are instantaneous equation/initialization contracts, not a time-stepping
policy or a claim about derivatives of rounded machine arithmetic. -/
noncomputable section
namespace Rumoca.Solve
open Rumoca.Tensor Solve.Tensor

def PointwiseIVP.Equation (p : PointwiseIVP shape) (state input derivative : Value ℝ shape)
    (matrix : Matrix (Fin shape.volume) (Fin shape.volume) ℝ) : Prop :=
  derivative = p.problem.rhs AD.realOps 0 1 state input ∧
    match p.diagonal with
    | none => True
    | some program => matrix = (program.eval AD.realOps 0 1 (p.problem.environment state input)).toMatrix

def PointwiseIVP.Initial (p : PointwiseIVP shape) (state : Value ℝ shape) : Prop :=
  state = p.problem.initial AD.realOps 0 1

theorem PointwiseIVP.output_correct (p : PointwiseIVP shape) (ops : ScalarOps α) (zero one : α)
    (state input : Value α shape) : p.problem.outputs ops zero one state input = state := rfl

end Rumoca.Solve
