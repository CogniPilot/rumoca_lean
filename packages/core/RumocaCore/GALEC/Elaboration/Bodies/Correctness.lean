import RumocaCore.GALEC.Elaboration.Bodies.Lowering
import RumocaCore.GALEC.Elaboration.Bodies.Source

/-! Universal execution correspondence for the actual structurally lowered
source body. Arithmetic may be partial or nondeterministic. This composes
relations and frames, not equalities of totalized execution functions. -/
namespace Rumoca.GALEC.Elaboration.Bodies
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

mutual
theorem statement_correct (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (source : AST.Statement) (stmt : Statement inputs outputs bounds)
    (typed : StatementElaborates table HasShape ceiling names source stmt)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Env α outputs) :
    Source.statement table HasShape ceiling step zero one @input names @env source @before @after ↔
      stmt.Executes step zero one @input @env @before @after := by
  cases typed with
  | assign assignment =>
    cases assignment with
    | assign target value =>
      rw [Source.statement]
      exact AssignmentLowering.lowering_correct (.assign target value)
        step zero one @input @env @before @after
  | loop header body =>
    rw [Source.loop_finite_iff table lookupShape HasShape correct ceiling step zero one
      @input names @env header _ @before @after]
    apply Iteration.executes_congr (σ := Env α outputs)
    intro index current next
    exact statements_correct table lookupShape HasShape correct ceiling _ _ _ body
      step zero one @input (IteratorEnv.push index @env) @current @next
termination_by sizeOf source

theorem statements_correct (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (typed : BodyElaborates table HasShape ceiling names sources stmt)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Env α outputs) :
    Source.statements table HasShape ceiling step zero one @input names @env sources @before @after ↔
      stmt.Executes step zero one @input @env @before @after := by
  cases typed with
  | nil => rw [Source.statements]; rfl
  | cons firstTyped restTyped =>
    rw [Source.statements]
    constructor
    · rintro ⟨middle, first, rest⟩
      exact ⟨middle,
        (statement_correct table lookupShape HasShape correct ceiling names _ _ firstTyped
          step zero one @input @env @before @middle).mp first,
        (statements_correct table lookupShape HasShape correct ceiling names _ _ restTyped
          step zero one @input @env @middle @after).mp rest⟩
    · rintro ⟨middle, first, rest⟩
      exact ⟨middle,
        (statement_correct table lookupShape HasShape correct ceiling names _ _ firstTyped
          step zero one @input @env @before @middle).mpr first,
        (statements_correct table lookupShape HasShape correct ceiling names _ _ restTyped
          step zero one @input @env @middle @after).mpr rest⟩
termination_by sizeOf sources
end

theorem source_to_statement (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (source : AST.Statement) (stmt : Statement inputs outputs bounds)
    (lowered : statement table lookupShape ceiling names source = some stmt)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Env α outputs) :
    Source.statement table HasShape ceiling step zero one @input names @env source @before @after ↔
      stmt.Executes step zero one @input @env @before @after :=
  statement_correct table lookupShape HasShape correct ceiling names source stmt
    ((statement_iff table lookupShape HasShape correct ceiling names source stmt).mp lowered)
    step zero one @input @env @before @after

theorem source_to_body (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (lowered : statements table lookupShape ceiling names sources = some stmt)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Env α outputs) :
    Source.statements table HasShape ceiling step zero one @input names @env sources @before @after ↔
      stmt.Executes step zero one @input @env @before @after :=
  statements_correct table lookupShape HasShape correct ceiling names sources stmt
    ((statements_iff table lookupShape HasShape correct ceiling names sources stmt).mp lowered)
    step zero one @input @env @before @after

end Rumoca.GALEC.Elaboration.Bodies
