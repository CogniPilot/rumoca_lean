import RumocaCore.GALEC.VectorBodies
import RumocaCore.GALEC.MatrixBodies

/-! A typed clear-then-scatter body for a certified rank-one coefficient
expression. Input rank and target matrix extents are explicit throughout. -/
namespace Rumoca.GALEC.VectorBodies
open Rumoca.Tensor Rumoca.Solve.Tensor Coefficients

def diagonal (source : Ref inputs ⟨[extent]⟩) (target : Ref outputs (matrixShape extent extent))
    (expression : ScalarExpr) : Statement inputs outputs bounds :=
  .seq (MatrixBodies.clearMatrix target) (scatter source target expression)

def diagonalValue (ops : ScalarOps α) (zero one : α) (expression : ScalarExpr)
    (input : Value α ⟨[extent]⟩) : Value α (matrixShape extent extent) :=
  TensorWrites.scatterWith (fun i => expression.eval ops zero one input[vectorIndex i])
    (Value.fill (matrixShape extent extent) zero)

theorem diagonalValue_get (ops : ScalarOps α) (zero one : α) (expression : ScalarExpr)
    (input : Value α ⟨[extent]⟩) (row col : Fin extent) :
    (diagonalValue ops zero one expression input)[matrixIndex (row, col)] =
      if row = col then expression.eval ops zero one input[vectorIndex row] else zero := by
  rw [diagonalValue, TensorWrites.scatterWith_get]
  congr 1
  exact Value.getElem_fill _ _ (matrixIndex (row, col)).isLt

noncomputable section

theorem diagonal_executes (source : Ref inputs ⟨[extent]⟩)
    (target : Ref outputs (matrixShape extent extent)) (expression : ScalarExpr)
    (input : Env Binary64.Value inputs) (iterators : IteratorEnv bounds)
    (before after : Env Binary64.Value outputs) :
    (diagonal source target expression).Executes Finite.Result Binary64.positiveZero Binary64.one
      input iterators before after ↔
    (∀ i : Fin extent, expression.inDomain (input source)[vectorIndex i]) ∧
    Env.Updates before target
      (diagonalValue Finite.ops Binary64.positiveZero Binary64.one expression (input source)) after := by
  change (∃ middle, (MatrixBodies.clearMatrix target).Executes Finite.Result
      Binary64.positiveZero Binary64.one input iterators before middle ∧
    (scatter source target expression).Executes Finite.Result
      Binary64.positiveZero Binary64.one input iterators middle after) ↔ _
  simp only [MatrixBodies.clear_matrix_executes, scatter_executes]
  constructor
  · rintro ⟨middle, clearFrame, domain, scatterFrame⟩
    have cleared : middle target = Value.fill (matrixShape extent extent) Binary64.positiveZero := clearFrame.1
    rw [cleared] at scatterFrame
    exact ⟨domain, scatterFrame.1, fun other different =>
      (scatterFrame.2 other different).trans (clearFrame.2 other different)⟩
  · rintro ⟨domain, frame⟩
    refine ⟨Env.update before target (Value.fill (matrixShape extent extent) Binary64.positiveZero),
      (Env.update_correct _ _ _ _).mpr rfl, domain, ?_, ?_⟩
    · simpa only [Env.update_same, diagonalValue] using frame.1
    · intro otherShape other different
      exact (frame.2 other different).trans
        (Env.update_other before target _ other different).symm

end
end Rumoca.GALEC.VectorBodies
