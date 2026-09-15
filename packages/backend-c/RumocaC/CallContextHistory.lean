import RumocaC.CallContext

namespace Rumoca.CCalls.Context
open CTree CMemory

/-- The suspended caller is retained literally beneath the current local
control. This witness is obtained from actual execution, not supplied at
subsequent nested calls. -/
def ThreadReady (P : Typed.State → Prop) (outer : Typed.Continuation)
    (tracked : Nat) (state : Concurrent.State) : Prop :=
  ∃ inner, state.threads tracked = some (inner.append outer) ∧ P inner

theorem call_origin (ready : ThreadReady P outer tracked state)
    (calling : state.threads tracked = some (.calling name args heap stack)) :
    ∃ innerStack, stack = innerStack.append outer ∧ P (.calling name args heap innerStack) := by
  obtain ⟨inner, selected, ready⟩ := ready
  have same := Option.some.inj (selected.symm.trans calling)
  cases inner with
  | calling function values memory innerStack =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Typed.State.calling.inj same
    exact ⟨innerStack, rfl, ready⟩
  | _ => contradiction

variable [CInterface] {E : Type}

/-- The real scheduler step provides the matching local step under the exact
saved caller. Other threads may change shared memory between any own steps. -/
theorem saved_step (program : Events.Program E) (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (Concurrent.withHeap state heap))
    (preserves : ∀ state events after, P state → Active state → Events.Step program state events after → P after)
    (ready : ThreadReady P outer tracked before)
    (active : Concurrent.BeforeReturn tracked outer before chosen)
    (actual : Concurrent.Step program before chosen events after) : ThreadReady P outer tracked after := by
  obtain ⟨inner, selected, ready⟩ := ready
  cases actual with
  | run found executed =>
    by_cases same : chosen = tracked
    · subst chosen
      cases Option.some.inj (found.symm.trans selected)
      have currentActive : Active (Concurrent.withHeap inner before.heap) := by
        apply active_of_suspended
        rw [← heap_append]
        exact fun exited => active rfl _ selected ((Concurrent.exit_withHeap _ _).mp exited)
      rw [heap_append] at executed
      obtain ⟨next, stepped, rfl⟩ := step_unappend program _ outer currentActive executed
      have following := preserves _ _ _ (heapStable inner ready before.heap) currentActive stepped
      refine ⟨Concurrent.control next, ?_, heapStable next following (fun _ => none)⟩
      simp [Concurrent.update, Concurrent.control, heap_append]
    · exact ⟨inner, by simpa [Concurrent.update, Ne.symm same] using selected, ready⟩

theorem interval_history (program : Events.Program E) (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (Concurrent.withHeap state heap))
    (preserves : ∀ state events after, P state → Active state → Events.Step program state events after → P after)
    (ready : ThreadReady P outer tracked before)
    (path : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ Concurrent.BeforeReturn tracked outer a chosen) before after) :
    ThreadReady P outer tracked after := by
  induction path with
  | refl => exact ready
  | next first rest ih =>
    obtain ⟨chosen, events, actual, active⟩ := first
    exact ih (saved_step program P heapStable preserves ready active actual)

end Rumoca.CCalls.Context
