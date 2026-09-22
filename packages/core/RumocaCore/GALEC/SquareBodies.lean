import RumocaCore.GALEC.VectorDiagonal
import RumocaCore.GALEC.SquareRealization

/-! The existing prepared square/AD profile expressed with reusable typed
loops. The original finite RHS execution supplies every coefficient domain;
no caller assumption silently drops the primal multiplication. -/
namespace Rumoca.GALEC.SquareBodies
open Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

def body (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) : Statement inputs outputs bounds :=
  .seq (pointwise source rhs squaredInput) (diagonal source jacobian doubledInput)

theorem targets_different (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) : Ref.position rhs ≠ Ref.position jacobian := by
  intro same
  obtain ⟨sameShape, _⟩ := Ref.position_agrees jacobian rhs same
  have rank := congrArg (fun shape : Shape => shape.dimensions.length) sameShape
  change 1 = 2 at rank
  omega

noncomputable section

theorem pointwise_source_executes (source : Ref inputs ⟨[extent]⟩) (target : Ref outputs ⟨[extent]⟩)
    (state : Value Binary64.Value ⟨[extent]⟩) (input : Env Binary64.Value inputs)
    (iterators : IteratorEnv bounds) (before after : Env Binary64.Value outputs) :
    (pointwise source target squaredInput).Executes Finite.Result Binary64.positiveZero Binary64.one
      input iterators before after ↔
    ∃ result, Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
      (Rumoca.ArrayProfile.environment state (input source)) result ∧ Env.Updates before target result after := by
  rw [pointwise_executes]
  apply exists_congr
  intro result
  apply and_congr_left
  intro _
  exact ((square_rhs_loop_iff state (input source) (before target) result).trans
    (squaredInput.pointwise_executes_iff (input source) (before target) result)).symm

theorem coefficient_domains_from_rhs (state input rhs : Value Binary64.Value ⟨[extent]⟩)
    (executed : Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
      (Rumoca.ArrayProfile.environment state input) rhs) :
    ∀ i : Fin extent, doubledInput.inDomain input[vectorIndex i] := by
  have source := square_from_finite_rhs state input rhs executed
  intro i
  exact ((doubledInput.executes_iff _ _).mp (source.2.2.2 (vectorIndex i))).1

/-- Exact successful finite execution of the whole typed body. Its domain
is the original ordered square RHS domain, not merely finite doubling.
The explicit final store also retains every unrelated binding. -/
theorem body_executes (source : Ref inputs ⟨[extent]⟩) (rhsTarget : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value inputs) (iterators : IteratorEnv bounds)
    (before after : Env Binary64.Value outputs) :
    (body source rhsTarget jacobian).Executes Finite.Result Binary64.positiveZero Binary64.one
      input iterators before after ↔
    ∃ rhs, Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
      (Rumoca.ArrayProfile.environment state (input source)) rhs ∧
      @after = @Env.update Binary64.Value outputs (matrixShape extent extent)
        (Env.update before rhsTarget rhs) jacobian
        (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput (input source)) := by
  change (∃ middle, (pointwise source rhsTarget squaredInput).Executes Finite.Result
      Binary64.positiveZero Binary64.one input iterators before middle ∧
    (diagonal source jacobian doubledInput).Executes Finite.Result
      Binary64.positiveZero Binary64.one input iterators middle after) ↔ _
  simp only [pointwise_source_executes source rhsTarget state, diagonal_executes]
  constructor
  · rintro ⟨middle, ⟨rhs, rhsExecution, rhsFrame⟩, _, jacobianFrame⟩
    refine ⟨rhs, rhsExecution, ?_⟩
    have first := (Env.update_correct _ _ _ _).mp rhsFrame
    have second := (Env.update_correct _ _ _ _).mp jacobianFrame
    rw [first] at second
    exact second
  · rintro ⟨rhs, rhsExecution, same⟩
    refine ⟨Env.update before rhsTarget rhs,
      ⟨rhs, rhsExecution, (Env.update_correct _ _ _ _).mpr rfl⟩,
      coefficient_domains_from_rhs state (input source) rhs rhsExecution,
      (Env.update_correct _ _ _ _).mpr same⟩

theorem jacobian_value_get (input : Value Binary64.Value ⟨[extent]⟩) (row col : Fin extent) :
    (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput input)[matrixIndex (row, col)] =
    if row = col then Binary64.roundedAdd input[vectorIndex row] input[vectorIndex row]
      else Binary64.positiveZero := by
  rw [diagonalValue_get]
  rfl

/-- Coordinate-wise agreement with the already AD-generated prepared matrix.
This is evaluator equality; successful source execution is retained separately
by `body_executes`, not inferred from this equation alone. -/
theorem jacobian_value_prepared (state input : Value Binary64.Value ⟨[extent]⟩)
    (row col : Fin extent) :
    (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput input)[matrixIndex (row, col)] =
    ((Rumoca.ArrayProfile.squareJacobianProgram ⟨[extent]⟩).eval
      Finite.ops Binary64.positiveZero Binary64.one (Rumoca.ArrayProfile.environment state input)).toMatrix
        (vectorIndex row) (vectorIndex col) := by
  rw [jacobian_value_get]
  simp only [DiagonalProgram.eval, Value.toMatrix_ofMatrix, Matrix.diagonal_apply]
  by_cases same : row = col
  · subst col
    simp only
    exact (Rumoca.ArrayProfile.ADExact.coefficients_eval_get state input (vectorIndex row)).symm
  · have different : vectorIndex row ≠ vectorIndex col := fun h => same (vectorIndex_injective h)
    simp only [if_neg same, if_neg different]
    rfl

/-- Whole-body observations include the original finite RHS, the prepared
AD matrix at corresponding rank-aware coordinates, and every unrelated binding. -/
theorem body_outputs (source : Ref inputs ⟨[extent]⟩) (rhsTarget : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value inputs) (iterators : IteratorEnv bounds)
    (before after : Env Binary64.Value outputs)
    (executed : (body source rhsTarget jacobian).Executes Finite.Result
      Binary64.positiveZero Binary64.one input iterators before after) :
    ∃ rhs, Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
      (Rumoca.ArrayProfile.environment state (input source)) rhs ∧
    after rhsTarget = rhs ∧
    (∀ row col : Fin extent, (after jacobian)[matrixIndex (row, col)] =
      ((Rumoca.ArrayProfile.squareJacobianProgram ⟨[extent]⟩).eval Finite.ops
        Binary64.positiveZero Binary64.one (Rumoca.ArrayProfile.environment state (input source))).toMatrix
          (vectorIndex row) (vectorIndex col)) ∧
    (∀ {otherShape} (other : Ref outputs otherShape),
      Ref.position other ≠ Ref.position rhsTarget → Ref.position other ≠ Ref.position jacobian →
      after other = before other) := by
  obtain ⟨rhs, rhsExecution, same⟩ :=
    (body_executes source rhsTarget jacobian state input iterators before after).mp executed
  refine ⟨rhs, rhsExecution, ?_, ?_, ?_⟩
  · have read := congrArg (fun env : Env Binary64.Value outputs => env rhsTarget) same
    simpa only [Env.update_other _ jacobian _ rhsTarget (targets_different rhsTarget jacobian),
      Env.update_same] using read
  · intro row col
    have read := congrArg (fun env : Env Binary64.Value outputs => env jacobian) same
    simp only [Env.update_same] at read
    rw [read]
    exact jacobian_value_prepared state (input source) row col
  · intro otherShape other outsideRhs outsideJacobian
    have read := congrArg (fun env : Env Binary64.Value outputs => env other) same
    simpa only [Env.update_other _ jacobian _ other outsideJacobian,
      Env.update_other before rhsTarget rhs other outsideRhs] using read

end
end Rumoca.GALEC.SquareBodies
