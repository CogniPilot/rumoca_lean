import RumocaC.ConcurrentCalls

/-! Reusable control invariants for an invocation interval ending before the original caller resumes. -/
namespace Rumoca.CCalls.Concurrent
open CTree CMemory
/-- The interval ends at the helper's original caller continuation. It does
not assert anything about the caller's later execution. -/
def Exit (stack : Typed.Continuation) (state : Typed.State) : Prop :=
  ∃ value heap, state = .returning value heap stack

theorem exit_withHeap (state : Typed.State) (heap : Heap) :
    Exit stack (Concurrent.withHeap state heap) ↔ Exit stack state := by
  cases state with
  | body state => cases state <;> simp [Exit, Concurrent.withHeap]
  | _ => simp [Exit, Concurrent.withHeap]

/-- Other threads may continue; the tracked invocation stops before its
return to the original caller is consumed. No later helper states are annotated. -/
def BeforeReturn (tracked : Nat) (stack : Typed.Continuation)
    (before : Concurrent.State) (chosen : Nat) : Prop :=
  chosen = tracked → ∀ saved, before.threads tracked = some saved → ¬ Exit stack saved

/-- Heap-stable control predicates lift through a tracked invocation interval.
The premise restricts when the original caller may resume, not intermediate
helper states or atomic outcomes. -/
theorem saved_predicate_step [CInterface] (program : Events.Program E)
    (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (Concurrent.withHeap state heap))
    (preserves : ∀ state events after, P state → ¬ Exit stack state →
      Events.Step program state events after → P after)
    (ready : ∃ saved, before.threads tracked = some saved ∧ P saved)
    (active : BeforeReturn tracked stack before chosen)
    (step : Concurrent.Step program before chosen events after) :
    ∃ saved, after.threads tracked = some saved ∧ P saved := by
  obtain ⟨saved, selected, ready⟩ := ready
  cases step with
  | run found executed =>
    by_cases same : chosen = tracked
    · subst chosen
      cases Option.some.inj (found.symm.trans selected)
      have running : ¬ Exit stack (Concurrent.withHeap saved before.heap) :=
        fun done => active rfl saved selected ((exit_withHeap saved before.heap).mp done)
      have following := preserves _ _ _ (heapStable saved ready before.heap) running executed
      exact ⟨_, by simp [Concurrent.update, Concurrent.control], heapStable _ following (fun _ => none)⟩
    · exact ⟨saved, by simpa [Concurrent.update, Ne.symm same] using selected, ready⟩


end Rumoca.CCalls.Concurrent
