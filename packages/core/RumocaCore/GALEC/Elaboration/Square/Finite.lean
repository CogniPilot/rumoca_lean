import RumocaCore.GALEC.Elaboration.Square.Layout

/-! Source-AST consequences for the already prepared finite square and AD
programs. This retains the original primal multiplication domain and exact
prepared Jacobian observations; it is not machine or actual-artifact evidence. -/
namespace Rumoca.GALEC.Elaboration.Square
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

/-- A name for the existing independent source semantics on the concrete AST,
declarations and constructed table, not execution of a lowered target. -/
def squareExecutes (extent ceiling : Nat) (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (squareFields extent))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (squareFields extent))) : Prop :=
  Bodies.Source.statements (Layout.bindings (squareFields extent))
    (Declarations.ShapeLookup.HasShape ceiling (squareDeclarations extent)) ceiling step zero one
    @input .nil @env (squareSource "u" "x" "J") @before @after

noncomputable section

theorem finite_source_iff (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling)
    (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (squareFields extent))) (env : IteratorEnv [])
    (before after : Env Binary64.Value (Layout.outputShapes (squareFields extent))) :
    squareExecutes extent ceiling Finite.Result Binary64.positiveZero Binary64.one
      @input @env @before @after ↔
    ∃ rhs, Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
      (Rumoca.ArrayProfile.environment state (input (squareInput extent))) rhs ∧
      @after = @Env.update Binary64.Value (Layout.outputShapes (squareFields extent))
        (matrixShape extent extent) (Env.update before (squareRhs extent) rhs) (squareJacobian extent)
        (diagonalValue Finite.ops Binary64.positiveZero Binary64.one doubledInput (input (squareInput extent))) :=
  (layout_source_executes positive within axisBound Finite.Result Binary64.positiveZero Binary64.one
    @input @env @before @after).trans
    (SquareBodies.body_executes (squareInput extent) (squareRhs extent) (squareJacobian extent)
      state @input @env @before @after)

theorem finite_source_outputs (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling)
    (state : Value Binary64.Value ⟨[extent]⟩)
    (input : Env Binary64.Value (Layout.inputShapes (squareFields extent))) (env : IteratorEnv [])
    (before after : Env Binary64.Value (Layout.outputShapes (squareFields extent)))
    (executed : squareExecutes extent ceiling Finite.Result Binary64.positiveZero Binary64.one
      @input @env @before @after) :
    ∃ rhs, Finite.Executes (Rumoca.ArrayProfile.squareProgram ⟨[extent]⟩)
      (Rumoca.ArrayProfile.environment state (input (squareInput extent))) rhs ∧
    after (squareRhs extent) = rhs ∧
    (∀ row col : Fin extent, (after (squareJacobian extent))[matrixIndex (row, col)] =
      ((Rumoca.ArrayProfile.squareJacobianProgram ⟨[extent]⟩).eval Finite.ops
        Binary64.positiveZero Binary64.one
        (Rumoca.ArrayProfile.environment state (input (squareInput extent)))).toMatrix
          (vectorIndex row) (vectorIndex col)) ∧
    (∀ {otherShape} (other : Ref (Layout.outputShapes (squareFields extent)) otherShape),
      Ref.position other ≠ Ref.position (squareRhs extent) →
      Ref.position other ≠ Ref.position (squareJacobian extent) → after other = before other) :=
  SquareBodies.body_outputs (squareInput extent) (squareRhs extent) (squareJacobian extent)
    state @input @env @before @after
    ((layout_source_executes positive within axisBound Finite.Result Binary64.positiveZero Binary64.one
      @input @env @before @after).mp executed)

end
end Rumoca.GALEC.Elaboration.Square
