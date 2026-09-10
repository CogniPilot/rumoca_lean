import Std

/-! Bounded parallel mapping with deterministic order. Only independent file
work is scheduled; there is no shared parser state or global source counter.
Lean's standard Task semantics erase scheduling from the logical result. -/
namespace Parser.Parallel

/-- At most `jobs - 1` tasks are spawned; each leaf maps its contiguous chunk
sequentially. The calling thread also works. No task is created per input file. -/
def map (jobs : Nat) (f : α → β) (inputs : List α) : List β :=
  if _h : jobs ≤ 1 ∨ inputs.length ≤ 1 then inputs.map f
  else
    let leftJobs := jobs / 2
    let split := inputs.length / 2
    let left := Task.spawn fun _ => map leftJobs f (inputs.take split)
    let right := map (jobs - leftJobs) f (inputs.drop split)
    left.get ++ right
  termination_by jobs
  decreasing_by all_goals omega

/-- Parallel execution has exactly the sequential values, errors and order,
for every input and every pure analysis function, not just the tiny grammar. -/
theorem map_eq (jobs : Nat) (f : α → β) (inputs : List α) :
    map jobs f inputs = inputs.map f := by
  induction jobs using Nat.strongRecOn generalizing inputs with
  | ind jobs ih =>
    rw [map]
    split
    · rfl
    · rename_i h
      have hl : jobs / 2 < jobs := by omega
      have hr : jobs - jobs / 2 < jobs := by omega
      simp only [Task.spawn, ih _ hl, ih _ hr]
      rw [← List.map_append, List.take_append_drop]

end Parser.Parallel
