import RumocaCore.GALEC.Statements

/-! Relational composition laws for existing indexed statements. These laws
do not optimize or recognize source bodies. Arithmetic may be partial or
nondeterministic; no total evaluator, native execution or counter policy is
assumed. All iterator environments and endpoint stores are quantified. -/
namespace Rumoca.GALEC.StatementRelations
open Rumoca.Tensor Rumoca.Solve.Tensor

def Equivalent (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (first second : Statement inputs outputs bounds) : Prop :=
  ∀ (env : IteratorEnv bounds) (before after : Env α outputs),
    first.Executes step zero one @input @env @before @after ↔
      second.Executes step zero one @input @env @before @after

namespace Equivalent
variable {step : BinaryOp → α → α → α → Prop} {zero one : α} {input : Env α inputs}

theorem refl (stmt : Statement inputs outputs bounds) :
    Equivalent step zero one @input stmt stmt := by
  intro env before after
  exact Iff.rfl

theorem symm {first second : Statement inputs outputs bounds}
    (related : Equivalent step zero one @input first second) :
    Equivalent step zero one @input second first := by
  intro env before after
  exact (related @env @before @after).symm

theorem trans {first second third : Statement inputs outputs bounds}
    (left : Equivalent step zero one @input first second)
    (right : Equivalent step zero one @input second third) :
    Equivalent step zero one @input first third := by
  intro env before after
  exact (left @env @before @after).trans (right @env @before @after)

end Equivalent

variable (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)

theorem seq_skip_right (stmt : Statement inputs outputs bounds) :
    Equivalent step zero one @input (.seq stmt .skip) stmt := by
  intro env before after
  change (∃ middle : Env α outputs,
    stmt.Executes step zero one @input @env @before @middle ∧ @after = @middle) ↔
      stmt.Executes step zero one @input @env @before @after
  constructor
  · rintro ⟨middle, executed, same⟩
    cases same
    exact executed
  · intro executed
    exact ⟨after, executed, rfl⟩

theorem seq_skip_left (stmt : Statement inputs outputs bounds) :
    Equivalent step zero one @input (.seq .skip stmt) stmt := by
  intro env before after
  change (∃ middle : Env α outputs, @middle = @before ∧
    stmt.Executes step zero one @input @env @middle @after) ↔
      stmt.Executes step zero one @input @env @before @after
  constructor
  · rintro ⟨middle, same, executed⟩
    cases same
    exact executed
  · intro executed
    exact ⟨before, rfl, executed⟩

theorem seq_associative (first second third : Statement inputs outputs bounds) :
    Equivalent step zero one @input (.seq (.seq first second) third)
      (.seq first (.seq second third)) := by
  intro env before after
  constructor
  · rintro ⟨middle, ⟨earlier, firstRun, secondRun⟩, thirdRun⟩
    exact ⟨earlier, firstRun, ⟨middle, secondRun, thirdRun⟩⟩
  · rintro ⟨earlier, firstRun, ⟨middle, secondRun, thirdRun⟩⟩
    exact ⟨middle, ⟨earlier, firstRun, secondRun⟩, thirdRun⟩

theorem seq_congr {first first' second second' : Statement inputs outputs bounds}
    (left : Equivalent step zero one @input first first')
    (right : Equivalent step zero one @input second second') :
    Equivalent step zero one @input (.seq first second) (.seq first' second') := by
  intro env before after
  constructor
  · rintro ⟨middle, firstRun, secondRun⟩
    exact ⟨middle, (left @env @before @middle).mp firstRun,
      (right @env @middle @after).mp secondRun⟩
  · rintro ⟨middle, firstRun, secondRun⟩
    exact ⟨middle, (left @env @before @middle).mpr firstRun,
      (right @env @middle @after).mpr secondRun⟩

/-- Lift body equivalence at the extended index context through every bounded
loop, including zero bound. The same index and current/next stores are used. -/
theorem bounded_congr (bound : Nat)
    {first second : Statement inputs outputs (bound :: bounds)}
    (related : Equivalent step zero one @input first second) :
    Equivalent step zero one @input (.bounded bound first) (.bounded bound second) := by
  intro env before after
  apply Iteration.executes_congr
  intro index current next
  exact related (IteratorEnv.push index @env) @current @next

end Rumoca.GALEC.StatementRelations
