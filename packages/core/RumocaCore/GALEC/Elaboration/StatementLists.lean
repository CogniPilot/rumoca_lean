import RumocaCore.GALEC.Elaboration.Assignments

/-! Reusable source-body composition. The statement compiler is a pure
compiler parameter; produced IR contains only existing skip/seq/statement
nodes. The independent relation retains every actual intermediate store. -/
namespace Rumoca.GALEC.Elaboration.StatementLists
open Rumoca.Tensor Rumoca.Solve.Tensor

def lower (lowerStatement : AST.Statement → Option (Statement inputs outputs bounds)) :
    List AST.Statement → Option (Statement inputs outputs bounds)
  | [] => some .skip
  | source :: rest => (lowerStatement source).bind fun first =>
      (lower lowerStatement rest).map (Statement.seq first)

inductive Elaborates
    (StatementElaborates : AST.Statement → Statement inputs outputs bounds → Prop) :
    List AST.Statement → Statement inputs outputs bounds → Prop where
  | nil : Elaborates StatementElaborates [] .skip
  | cons : StatementElaborates source first → Elaborates StatementElaborates rest remaining →
      Elaborates StatementElaborates (source :: rest) (.seq first remaining)

theorem lower_iff
    (lowerStatement : AST.Statement → Option (Statement inputs outputs bounds))
    (StatementElaborates : AST.Statement → Statement inputs outputs bounds → Prop)
    (correct : ∀ source stmt, lowerStatement source = some stmt ↔ StatementElaborates source stmt)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds) :
    lower lowerStatement sources = some stmt ↔ Elaborates StatementElaborates sources stmt := by
  induction sources generalizing stmt with
  | nil =>
    constructor
    · intro found; cases Option.some.inj found; exact .nil
    · intro typed; cases typed; rfl
  | cons source rest ih =>
    simp only [lower, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    constructor
    · rintro ⟨first, firstLowered, remaining, restLowered, same⟩
      cases same
      exact .cons ((correct source first).mp firstLowered) ((ih remaining).mp restLowered)
    · intro typed
      cases typed with
      | cons firstTyped restTyped =>
        exact ⟨_, (correct _ _).mpr firstTyped, _, (ih _).mpr restTyped, rfl⟩

/-- Independent sequential source execution for arbitrary statement relations,
including partial and nondeterministic bodies. -/
inductive Executes (executeStatement : AST.Statement → σ → σ → Prop) : List AST.Statement → σ → σ → Prop where
  | nil (state : σ) : Executes executeStatement [] state state
  | cons : executeStatement source before middle → Executes executeStatement rest middle after →
      Executes executeStatement (source :: rest) before after

theorem execution_correct
    (StatementElaborates : AST.Statement → Statement inputs outputs bounds → Prop)
    (executeStatement : AST.Statement → Env α outputs → Env α outputs → Prop)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds)
    (correct : ∀ source stmt, StatementElaborates source stmt → ∀ before after : Env α outputs,
      executeStatement source @before @after ↔ stmt.Executes step zero one @input @env @before @after)
    (typed : Elaborates StatementElaborates sources stmt) (before after : Env α outputs) :
    Executes executeStatement sources @before @after ↔ stmt.Executes step zero one @input @env @before @after := by
  induction typed generalizing before after with
  | nil =>
    constructor
    · intro executed; cases executed; rfl
    · intro same
      change @after = @before at same
      cases same
      exact .nil _
  | cons firstTyped restTyped ih =>
    constructor
    · intro executed
      cases executed with
      | cons head tail =>
        exact ⟨_, (correct _ _ firstTyped _ _).mp head, (ih _ _).mp tail⟩
    · rintro ⟨middle, head, tail⟩
      exact .cons ((correct _ _ firstTyped _ _).mpr head) ((ih _ _).mpr tail)

def assignments (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (sources : List AST.Statement) := lower (AssignmentLowering.lower table names) sources

theorem assignments_iff (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds) :
    assignments table names sources = some stmt ↔
      Elaborates (AssignmentLowering.Elaborates table names) sources stmt :=
  lower_iff _ _ (AssignmentLowering.lower_iff table names) sources stmt

theorem assignments_execute (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (sources : List AST.Statement) (stmt : Statement inputs outputs bounds)
    (lowered : assignments table names sources = some stmt)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (before after : Env α outputs) :
    Executes (AssignmentLowering.Executes table names step zero one @input @env)
        sources @before @after ↔ stmt.Executes step zero one @input @env @before @after :=
  execution_correct _ _ step zero one @input @env
    (fun _ _ typed before after => AssignmentLowering.lowering_correct typed step zero one @input @env @before @after)
    ((assignments_iff table names sources stmt).mp lowered) @before @after

end Rumoca.GALEC.Elaboration.StatementLists
