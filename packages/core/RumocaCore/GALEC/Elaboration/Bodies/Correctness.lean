import RumocaCore.GALEC.Elaboration.Bodies.Lowering
import RumocaCore.GALEC.Elaboration.Bodies.Source

/-! Universal execution correspondence for the actual structurally lowered
source body, for the data relation and for execution with error signals.
Arithmetic may be partial or nondeterministic. This composes relations and
frames, not equalities of totalized execution functions. -/
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
  | branch chosen =>
    obtain ⟨condition, yes, no, rfl⟩ := branches_branch chosen
    simp only [Source.statement, Statement.Executes]
  | loop header body =>
    rw [Source.loop_finite_iff table lookupShape HasShape correct ceiling step zero one
      @input names @env header _ @before @after]
    apply Iteration.executes_congr (σ := Env α outputs)
    intro index current next
    exact statements_correct table lookupShape HasShape correct ceiling _ _ _ body
      step zero one @input (IteratorEnv.push index @env) @current @next
  | signal _ =>
    simp only [Source.statement, Statement.Executes]
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

mutual
/-- Execution with error signals of the actual source statement is execution
of its lowered statement, for every arithmetic and finiteness interpretation. -/
theorem statement_runs (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (source : AST.Statement) (stmt : Statement inputs outputs bounds)
    (typed : StatementElaborates table HasShape ceiling names source stmt)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Signaled α outputs) :
    Source.run table HasShape ceiling step finite zero one @input names @env source before after ↔
      stmt.Runs step finite zero one @input @env before after := by
  match source, typed with
  | _, .assign assignment =>
    cases assignment with
    | assign target value =>
      rw [Source.run]
      exact and_congr_left fun _ => AssignmentLowering.lowering_correct (.assign target value)
        step zero one @input @env @before.1 @after.1
  | .ifThen (first :: rest) otherwise, .branch chosen =>
    rw [Source.run]
    exact branches_runs table lookupShape HasShape correct ceiling names _ otherwise stmt chosen
      step finite zero one @input @env before after
  | .forLoop binder start stride stop body, .loop header typedBody =>
    rw [Source.loop_run_iff table lookupShape HasShape correct ceiling step finite zero one
      @input names @env header _ before after]
    apply Iteration.executes_congr (σ := Signaled α outputs)
    intro index current next
    exact statements_runs table lookupShape HasShape correct ceiling _ _ _ typedBody
      step finite zero one @input (IteratorEnv.push index @env) current next
  | .signal (first :: rest), .signal denoted =>
    rw [Source.run]
    constructor
    · rintro ⟨set, again, rfl⟩
      cases SignalNames.denotes_unique denoted again
      rfl
    · intro same
      exact ⟨_, denoted, same⟩
termination_by sizeOf source

theorem branches_runs (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List (AST.Condition × List AST.Statement)) (otherwise : Option (List AST.Statement))
    (stmt : Statement inputs outputs bounds)
    (typed : BranchesElaborates table HasShape ceiling names sources otherwise stmt)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Signaled α outputs) :
    Source.runBranches table HasShape ceiling step finite zero one @input names @env sources otherwise
        before after ↔
      stmt.Runs step finite zero one @input @env before after := by
  match sources, otherwise, typed with
  | [], none, .none =>
    rw [Source.runBranches]
    rfl
  | [], some body, .otherwise typedBody =>
    rw [Source.runBranches]
    exact statements_runs table lookupShape HasShape correct ceiling names body stmt typedBody
      step finite zero one @input @env before after
  | (test, body) :: rest, otherwise, .cons tested typedBody typedRest =>
    rw [Source.runBranches]
    simp only [Statement.Runs, ConditionLowering.enters_correct tested,
      ConditionLowering.fails_correct tested]
    apply or_congr
    · constructor
      · rintro ⟨entry, ⟨holds, rfl⟩, ran⟩
        exact ⟨holds, (statements_runs table lookupShape HasShape correct ceiling names body _
          typedBody step finite zero one @input @env _ after).mp ran⟩
      · rintro ⟨holds, ran⟩
        exact ⟨_, ⟨holds, rfl⟩, (statements_runs table lookupShape HasShape correct ceiling names body _
          typedBody step finite zero one @input @env _ after).mpr ran⟩
    · exact and_congr_right fun _ =>
        branches_runs table lookupShape HasShape correct ceiling names rest otherwise _ typedRest
          step finite zero one @input @env before after
termination_by sizeOf sources + sizeOf otherwise

theorem statements_runs (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (typed : BodyElaborates table HasShape ceiling names sources stmt)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Signaled α outputs) :
    Source.runs table HasShape ceiling step finite zero one @input names @env sources before after ↔
      stmt.Runs step finite zero one @input @env before after := by
  match sources, typed with
  | [], .nil =>
    rw [Source.runs]
    rfl
  | source :: rest, .cons firstTyped restTyped =>
    rw [Source.runs]
    constructor
    · rintro ⟨middle, first, remaining⟩
      exact ⟨middle,
        (statement_runs table lookupShape HasShape correct ceiling names _ _ firstTyped
          step finite zero one @input @env before middle).mp first,
        (statements_runs table lookupShape HasShape correct ceiling names _ _ restTyped
          step finite zero one @input @env middle after).mp remaining⟩
    · rintro ⟨middle, first, remaining⟩
      exact ⟨middle,
        (statement_runs table lookupShape HasShape correct ceiling names _ _ firstTyped
          step finite zero one @input @env before middle).mpr first,
        (statements_runs table lookupShape HasShape correct ceiling names _ _ restTyped
          step finite zero one @input @env middle after).mpr remaining⟩
termination_by sizeOf sources
end

theorem source_runs_body (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (ceiling : Nat) {bounds : List Nat} (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (lowered : statements table lookupShape ceiling names sources = some stmt)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Signaled α outputs) :
    Source.runs table HasShape ceiling step finite zero one @input names @env sources before after ↔
      stmt.Runs step finite zero one @input @env before after :=
  statements_runs table lookupShape HasShape correct ceiling names sources stmt
    ((statements_iff table lookupShape HasShape correct ceiling names sources stmt).mp lowered)
    step finite zero one @input @env before after

end Rumoca.GALEC.Elaboration.Bodies
