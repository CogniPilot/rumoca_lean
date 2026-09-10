import RumocaCore.Solve.IVP

/-! Declaration data co-owned with an executable IVP. This is a minimal
deployment root, not an FMI-specific value-reference table. A backend takes
this one value; it must not accept a second AST or independent metadata list.
-/
namespace Rumoca.Solve
open Rumoca.Tensor

inductive VariableId where
  | state
  | input
  deriving Repr, BEq, DecidableEq

inductive Causality where
  | input
  | output
  deriving Repr, BEq, DecidableEq

/-- The two declarations of the admitted driven profile. Their semantic IDs
are constructors; their source names are presentation data only. -/
structure ModelData where
  problem : IVP
  output_shape : problem.outputShape = problem.stateShape
  output_is_state : HEq problem.output
    (Solve.Tensor.Program.ret (Solve.Tensor.Ref.here :
      Solve.Tensor.Ref [problem.stateShape, problem.inputShape] problem.stateShape))
  stateName : String
  inputName : String
  distinct : stateName ≠ inputName

def ModelData.name (m : ModelData) : VariableId → String
  | .state => m.stateName
  | .input => m.inputName

def ModelData.shape (m : ModelData) : VariableId → Shape
  | .state => m.problem.stateShape
  | .input => m.problem.inputShape

/-- Causality is orthogonal to the state's role as an IVP unknown. The small
profile exposes that state directly; a backend does not create another state
variable for the output. -/
def ModelData.causality (_ : ModelData) : VariableId → Causality
  | .state => .output
  | .input => .input

theorem ModelData.names_unique (m : ModelData) : Function.Injective m.name := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact False.elim (m.distinct h)
  · exact False.elim (m.distinct h.symm)
  · rfl

end Rumoca.Solve
