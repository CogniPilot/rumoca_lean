import RumocaC.CallIntervals

/-! Heap-dependent control invariants across actual shared invocation intervals. -/
noncomputable section
namespace Rumoca.CCalls.Concurrent
open CTree CMemory

/-- A heap-dependent predicate on the tracked invocation lifts through a
shared scheduler step. Its own transition preserves the predicate; interference
must preserve it only when another thread is selected. -/
theorem framed_predicate_step [CInterface] (program : Events.Program E)
    (P : Typed.State → Prop) (before after : State) (tracked chosen : Nat)
    (preserves : ∀ state events target, P state → ¬ Exit stack state →
      Events.Step program state events target → P target)
    (interference : chosen ≠ tracked → ∀ saved, before.threads tracked = some saved →
      P (withHeap saved before.heap) → P (withHeap saved after.heap))
    (ready : ∃ saved, before.threads tracked = some saved ∧ P (withHeap saved before.heap))
    (active : BeforeReturn tracked stack before chosen)
    (step : Step program before chosen events after) :
    ∃ saved, after.threads tracked = some saved ∧ P (withHeap saved after.heap) := by
  obtain ⟨saved, selected, ready⟩ := ready
  cases step with
  | @run current result effects found executed =>
    by_cases same : chosen = tracked
    · subst chosen
      cases Option.some.inj (found.symm.trans selected)
      have running : ¬ Exit stack (withHeap saved before.heap) :=
        fun done => active rfl saved selected ((exit_withHeap saved before.heap).mp done)
      have following := preserves _ _ _ ready running executed
      exact ⟨control result, by simp [update], by simpa only [control_resume, withHeap_original] using following⟩
    · exact ⟨saved, by simpa [update, Ne.symm same] using selected, interference same saved selected ready⟩

end Rumoca.CCalls.Concurrent
