import RumocaCore.GALEC.Elaboration.Square.Layout
import RumocaCore.GALEC.Elaboration.Square.Outcomes

/-! Source-AST consequences of the checked DoStep body on the concrete square
declarations and table. Execution with error signals starts with no signal
set. When every product and sum is finite it retains the original finite
primal domain, exact whole-store updates and the prepared AD matrix, and sets
no signal; otherwise it sets `OVERFLOW` and leaves the store unchanged. This is
not machine or actual-artifact evidence. -/
namespace Rumoca.GALEC.Elaboration.Square
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

/-- The independent source semantics with error signals of the checked DoStep
body on the concrete AST, declarations and constructed table. -/
def checkedRuns (extent ceiling : Nat) (step : BinaryOp → α → α → α → Prop) (finite : α → Prop)
    (zero one : α) (input : Env α (Layout.inputShapes (squareFields extent))) (env : IteratorEnv [])
    (before after : Signaled α (Layout.outputShapes (squareFields extent))) : Prop :=
  Bodies.Source.runs (Layout.bindings (squareFields extent))
    (Declarations.ShapeLookup.HasShape ceiling (squareDeclarations extent)) ceiling step finite
    zero one @input .nil @env (checkedSource "u" Names.state "J") before after

noncomputable section

/-- Exactly two outcomes for every finite input store: all checks finite, no
signal and the existing square/AD update; or `OVERFLOW` and the store unchanged. -/
theorem checked_source_outcomes (positive : 0 < extent) (within : extent ≤ ceiling)
    (axisBound : 2 ≤ ceiling) (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (squareFields extent))) (env : IteratorEnv [])
    (before : Env Binary64.Value (Layout.outputShapes (squareFields extent)))
    (after : Signaled Binary64.Value (Layout.outputShapes (squareFields extent))) :
    checkedRuns extent ceiling Finite.Result (fun _ => True) Binary64.positiveZero Binary64.one
      @input @env ⟨@before, SignalSet.empty⟩ after ↔
    (Checked (input (squareInput extent)) ∧ after.2 = SignalSet.empty ∧
      ∃ rhs, Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
        (Rumoca.ArrayProfile.environment state (input (squareInput extent))) rhs ∧
        @after.1 = @Env.update Binary64.Value (Layout.outputShapes (squareFields extent))
          (matrixShape extent extent) (Env.update before (squareRhs extent) rhs) (squareJacobian extent)
          (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput
            (input (squareInput extent)))) ∨
    (¬ Checked (input (squareInput extent)) ∧ after = ⟨@before, overflowSet⟩) :=
  (layout_source_runs positive within axisBound Finite.Result (fun _ => True) Binary64.positiveZero
    Binary64.one @input @env _ after).trans
    (checked_outcomes (squareInput extent) (squareRhs extent) (squareJacobian extent) state
      @input @env @before after)

/-- The finite outcome exposes the original finite RHS, the prepared AD matrix
at rank-aware coordinates, an unchanged frame and no signal. -/
theorem checked_source_outputs (positive : 0 < extent) (within : extent ≤ ceiling)
    (axisBound : 2 ≤ ceiling) (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (squareFields extent))) (env : IteratorEnv [])
    (before : Env Binary64.Value (Layout.outputShapes (squareFields extent)))
    (after : Signaled Binary64.Value (Layout.outputShapes (squareFields extent)))
    (executed : checkedRuns extent ceiling Finite.Result (fun _ => True) Binary64.positiveZero
      Binary64.one @input @env ⟨@before, SignalSet.empty⟩ after)
    (checked : Checked (input (squareInput extent))) :
    after.2 = SignalSet.empty ∧
    ∃ rhs, Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
      (Rumoca.ArrayProfile.environment state (input (squareInput extent))) rhs ∧
    after.1 (squareRhs extent) = rhs ∧
    (∀ row col : Fin extent, (after.1 (squareJacobian extent))[matrixIndex (row, col)] =
      ((Rumoca.ArrayProfile.squareJacobianProgram ⟨[extent]⟩).eval Finite.ops
        Binary64.positiveZero Binary64.one
        (Rumoca.ArrayProfile.environment state (input (squareInput extent)))).toMatrix
          (vectorIndex row) (vectorIndex col)) ∧
    (∀ {otherShape} (other : Ref (Layout.outputShapes (squareFields extent)) otherShape),
      Ref.position other ≠ Ref.position (squareRhs extent) →
      Ref.position other ≠ Ref.position (squareJacobian extent) → after.1 other = before other) := by
  rcases (checked_source_outcomes positive within axisBound state input env before after).mp executed with
    ⟨_, kept, rhs, ran, updated⟩ | ⟨unchecked, _⟩
  · refine ⟨kept, SquareBodies.body_outputs (squareInput extent) (squareRhs extent)
      (squareJacobian extent) state @input @env @before @after.1 ?_⟩
    exact (SquareBodies.body_executes (squareInput extent) (squareRhs extent) (squareJacobian extent)
      state @input @env @before @after.1).mpr ⟨rhs, ran, updated⟩
  · exact absurd checked unchecked

/-- The overflow outcome sets exactly `OVERFLOW` and writes no storage. -/
theorem checked_source_unchanged (positive : 0 < extent) (within : extent ≤ ceiling)
    (axisBound : 2 ≤ ceiling) (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (squareFields extent))) (env : IteratorEnv [])
    (before : Env Binary64.Value (Layout.outputShapes (squareFields extent)))
    (after : Signaled Binary64.Value (Layout.outputShapes (squareFields extent)))
    (executed : checkedRuns extent ceiling Finite.Result (fun _ => True) Binary64.positiveZero
      Binary64.one @input @env ⟨@before, SignalSet.empty⟩ after)
    (unchecked : ¬ Checked (input (squareInput extent))) :
    after = ⟨@before, overflowSet⟩ := by
  rcases (checked_source_outcomes positive within axisBound state input env before after).mp executed with
    ⟨checked, _⟩ | ⟨_, same⟩
  · exact absurd checked unchecked
  · exact same

end
end Rumoca.GALEC.Elaboration.Square
