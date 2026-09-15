import RumocaC.InvocationLedger

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory
noncomputable section
variable [CInterface] {E : Type}

/-- The control invariant is indexed by the recorded enclosing invocation,
including its original public entry, rather than by an invented current root. -/
def Controls (P : Invocation → Typed.State → Prop) (state : State) : Prop :=
  ∀ thread saved call, state.runtime.threads thread = some saved → state.ledger.active thread = some call → P call saved

theorem step_controls (program : Events.Program E) (policy : Host.Policy)
    (P : Invocation → Typed.State → Prop)
    (heapStable : ∀ call state, P call state → ∀ heap, P call (Concurrent.withHeap state heap))
    (entry : ∀ serial state thread name args, policy.admit state thread name args →
      P ⟨serial, name, args⟩ (.calling name args state.heap .done))
    (preserves : ∀ call before events after, P call before → Events.Step program before events after → P call after)
    (ready : Controls P before) (step : Step program policy before ticks after) : Controls P after := by
  cases step with
  | @record state thread action following ledger actual =>
    cases actual with
    | invoke idle admitted =>
      intro other saved call found active
      by_cases same : other = thread
      · subst other
        simp only [Concurrent.update, ↓reduceIte, Option.some.injEq] at found
        simp only [advance, bind, ↓reduceIte, Option.some.injEq] at active
        subst saved
        subst call
        exact heapStable _ _ (entry ledger.next state thread _ _ admitted) _
      · exact ready other saved call
          (by simpa only [Concurrent.update, if_neg same] using found)
          (by simpa only [advance, bind, if_neg same] using active)
    | execute executed =>
      cases executed with
      | run selected executed =>
        intro other saved call found active
        by_cases same : other = thread
        · subst other
          simp only [Concurrent.update, ↓reduceIte, Option.some.injEq] at found
          subst saved
          exact heapStable _ _ (preserves call _ _ _ (heapStable _ _ (ready _ _ _ selected active) _) executed) _
        · exact ready other saved call (by simpa only [Concurrent.update, if_neg same] using found) active
    | complete halted =>
      intro other saved call found active
      by_cases same : other = thread
      · subst other
        simp [Host.retire] at found
      · exact ready other saved call (by simpa only [Host.retire, if_neg same] using found)
          (by simpa only [advance, bind, if_neg same] using active)
    | memory => exact ready

theorem history_controls (program : Events.Program E) (policy : Host.Policy)
    (P : Invocation → Typed.State → Prop)
    (heapStable : ∀ call state, P call state → ∀ heap, P call (Concurrent.withHeap state heap))
    (entry : ∀ serial state thread name args, policy.admit state thread name args →
      P ⟨serial, name, args⟩ (.calling name args state.heap .done))
    (preserves : ∀ call before events after, P call before → Events.Step program before events after → P call after)
    (ready : Controls P before)
    (path : Transition.Events.Reaches (Step program policy) before ticks after) : Controls P after := by
  induction path with
  | refl => exact ready
  | next first rest ih => exact ih (step_controls program policy P heapStable entry preserves ready first)

end
end Rumoca.CCalls.Host.Recording
