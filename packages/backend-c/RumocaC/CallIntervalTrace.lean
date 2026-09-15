import RumocaC.CallIntervals

namespace Rumoca.CCalls.Concurrent
open CTree CMemory

/-- Preserve the actual scheduler's thread/event labels while stopping the
tracked invocation before its original caller consumes the return. -/
def IntervalStep [CInterface] (program : Events.Program E) (tracked : Nat) (stack : Typed.Continuation)
    (before : State) (ticks : List (Nat × List E)) (after : State) : Prop :=
  ∃ chosen events, ticks = [(chosen, events)] ∧
    Step program before chosen events after ∧ BeforeReturn tracked stack before chosen

def ownTrace (tracked : Nat) (ticks : List (Nat × List E)) : List E :=
  ticks.flatMap fun tick => if tick.1 = tracked then tick.2 else []

theorem ownTrace_append (tracked : Nat) (first rest : List (Nat × List E)) :
    ownTrace tracked (first ++ rest) = ownTrace tracked first ++ ownTrace tracked rest :=
  List.flatMap_append

variable [CInterface] {E : Type}

theorem interval_erases
    (path : Transition.Events.Reaches (IntervalStep program tracked stack) before ticks after) :
    Transition.Reaches (fun a b => ∃ chosen events,
      Step program a chosen events b ∧ BeforeReturn tracked stack a chosen) before after := by
  induction path with
  | refl => exact .refl _
  | next first rest ih =>
    obtain ⟨chosen, events, _, actual, active⟩ := first
    exact .next ⟨chosen, events, actual, active⟩ ih

/-- A heap-stable own-control invariant can establish both silence of the
tracked invocation and preservation under other threads' actual C effects. -/
theorem silent_saved_step (program : Events.Program E) (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (withHeap state heap))
    (preserves : ∀ state events after, P state → ¬ Exit stack state →
      Events.Step program state events after → events = [] ∧ P after)
    (ready : ∃ saved, before.threads tracked = some saved ∧ P saved)
    (active : BeforeReturn tracked stack before chosen)
    (actual : Step program before chosen events after) :
    (chosen = tracked → events = []) ∧
      ∃ saved, after.threads tracked = some saved ∧ P saved := by
  refine ⟨?_, saved_predicate_step program P heapStable
    (fun state events after ready active step => (preserves state events after ready active step).2)
    ready active actual⟩
  intro same
  subst chosen
  obtain ⟨saved, selected, ready⟩ := ready
  cases actual with
  | run found executed =>
    cases Option.some.inj (found.symm.trans selected)
    exact (preserves _ _ _ (heapStable saved ready before.heap)
      (fun done => active rfl saved selected ((exit_withHeap saved before.heap).mp done)) executed).1

theorem silent_interval_history (program : Events.Program E) (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (withHeap state heap))
    (preserves : ∀ state events after, P state → ¬ Exit stack state →
      Events.Step program state events after → events = [] ∧ P after)
    (ready : ∃ saved, before.threads tracked = some saved ∧ P saved)
    (path : Transition.Events.Reaches (IntervalStep program tracked stack) before ticks after) :
    ownTrace tracked ticks = [] ∧ ∃ saved, after.threads tracked = some saved ∧ P saved := by
  induction path with
  | refl => exact ⟨rfl, ready⟩
  | next first rest ih =>
    obtain ⟨chosen, events, rfl, actual, active⟩ := first
    obtain ⟨silent, next⟩ := silent_saved_step program P heapStable preserves ready active actual
    obtain ⟨laterSilent, ready⟩ := ih next
    refine ⟨?_, ready⟩
    rw [ownTrace_append, laterSilent]
    by_cases same : chosen = tracked
    · simp [ownTrace, same, silent same]
    · simp [ownTrace, same]

end Rumoca.CCalls.Concurrent
