import RumocaCore.GALEC.Elaboration.Targets
import RumocaCore.GALEC.Elaboration.Locations
import RumocaCore.GALEC.Elaboration.Expressions

/-! Assignment lowering from the actual AST. Source execution specifies a
writable address, RHS execution, an independent tensor-cell write and the
whole-environment frame. It does not call target Statement execution. -/
namespace Rumoca.GALEC.Elaboration
open Rumoca.Tensor Rumoca.Solve.Tensor

def Target.location (target : Target outputs bounds) (env : IteratorEnv bounds) :
    Location inputs outputs :=
  ⟨target.shape, .writable target.ref, target.indices.eval env⟩

theorem TargetLowering.locating_correct
    {table : BindingTable inputs outputs} {names : IteratorNames bounds}
    {source : AST.Reference} {target : Target outputs bounds}
    (typed : TargetLowering.Elaborates table names source target)
    (env : IteratorEnv bounds) (location : Location inputs outputs) :
    Location.Evaluates table names env source location ↔ location = target.location env := by
  cases typed with
  | writable reference => exact Location.lowering_correct reference env location

namespace AssignmentLowering

def lower (table : BindingTable inputs outputs) (names : IteratorNames bounds) :
    AST.Statement → Option (Statement inputs outputs bounds)
  | .assign target rhs =>
      (TargetLowering.lower table names target).bind fun destination =>
        (ExpressionLowering.lower table names rhs).map
          fun value => .assign destination.ref destination.indices value
  | .forLoop .. => none

inductive Elaborates (table : BindingTable inputs outputs) (names : IteratorNames bounds) :
    AST.Statement → Statement inputs outputs bounds → Prop where
  | assign {target : Target outputs bounds} {term : ScalarTerm inputs outputs bounds}
      (destination : TargetLowering.Elaborates table names sourceTarget target)
      (value : ExpressionLowering.Elaborates table names sourceValue term) :
      Elaborates table names (.assign sourceTarget sourceValue)
        (.assign target.ref target.indices term)

theorem lower_iff (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Statement) (stmt : Statement inputs outputs bounds) :
    lower table names source = some stmt ↔ Elaborates table names source stmt := by
  constructor
  · intro found
    unfold lower at found
    split at found
    · rename_i sourceTarget sourceValue
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
      obtain ⟨target, targetLowered, term, valueLowered, same⟩ := found
      cases same
      exact .assign ((TargetLowering.lower_iff table names sourceTarget target).mp targetLowered)
        ((ExpressionLowering.lower_iff table names sourceValue term).mp valueLowered)
    · contradiction
  · intro typed
    cases typed with
    | assign destination value =>
      simp only [lower, (TargetLowering.lower_iff _ _ _ _).mpr destination, Option.bind_some,
        (ExpressionLowering.lower_iff _ _ _ _).mpr value, Option.map_some]

/-- Successful source assignment, including exact destination and frame.
Partial arithmetic may have no execution; no failure-state/signaling policy
or native memory aliasing guarantee is silently added here. -/
inductive Executes (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) :
    AST.Statement → Env α outputs → Env α outputs → Prop where
  | assign {sourceTarget : AST.Reference} {sourceValue : AST.Expr}
      {before after : Env α outputs} {shape : Shape} {ref : Ref outputs shape}
      {coordinate : Coordinates shape.dimensions} {result : α} {tensor : Value α shape}
      (located : Location.Evaluates table names @env sourceTarget ⟨shape, .writable ref, coordinate⟩)
      (value : ExpressionLowering.Evaluates table names step zero one @input @before @env sourceValue result)
      (written : TensorWrites.Writes (before ref) (Coordinate.index coordinate) result tensor)
      (stored : Env.Updates @before ref tensor @after) :
      Executes table names step zero one @input @env (.assign sourceTarget sourceValue) @before @after

variable {inputs outputs : List Shape} {bounds : List Nat}
  {table : BindingTable inputs outputs} {names : IteratorNames bounds}
  {source : AST.Statement} {stmt : Statement inputs outputs bounds}

theorem lowering_correct (typed : Elaborates table names source stmt)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Env α outputs) :
    Executes table names step zero one @input @env source @before @after ↔
      stmt.Executes step zero one @input @env @before @after := by
  cases typed with
  | assign destination valueTyped =>
    cases destination with
    | writable reference =>
      constructor
      · intro executed
        cases executed with
        | assign located value written stored =>
          have same := (Location.lowering_correct reference env _).mp located
          cases same
          exact ⟨_, _, (ExpressionLowering.lowering_correct valueTyped
            step zero one input before env _).mp value, written, stored⟩
      · rintro ⟨result, tensor, evaluated, written, stored⟩
        exact .assign (Location.lowering_sound reference env)
          ((ExpressionLowering.lowering_correct valueTyped step zero one input before env result).mpr evaluated)
          written stored

theorem source_to_statement (lowered : lower table names source = some stmt)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Env α outputs) :
    Executes table names step zero one @input @env source @before @after ↔
      stmt.Executes step zero one @input @env @before @after :=
  lowering_correct ((lower_iff table names source stmt).mp lowered) step zero one input env before after

end AssignmentLowering
end Rumoca.GALEC.Elaboration
