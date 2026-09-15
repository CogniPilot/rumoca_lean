import RumocaC.InvocationControl

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory

/-- A control property for one already-issued invocation. Later public calls
on the same reusable thread are distinct invocations, even with equal arguments. -/
def Selected (P : Typed.State → Prop) (tracked serial : Nat) (state : State) : Prop :=
  ∀ call saved, state.ledger.active tracked = some call → call.serial = serial →
    state.runtime.threads tracked = some saved → P saved

theorem advance_next (ledger : Ledger) (thread : Nat) (action : Action E) :
    ledger.next ≤ (advance ledger thread action).next := by
  cases action <;> simp [advance]

variable [CInterface] {E : Type}

/-- After an invocation has issued, a heap-stable control invariant follows
its actual execution through later host actions. Monotone issuance prevents a
new public entry from being mistaken for the tracked invocation. -/
theorem selected_step (program : Events.Program E) (policy : Host.Policy)
    (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (Concurrent.withHeap state heap))
    (preserves : ∀ before events after, P before → Events.Step program before events after → P after)
    (issued : serial < before.ledger.next) (ready : Selected P tracked serial before)
    (step : Step program policy before ticks after) :
    serial < after.ledger.next ∧ Selected P tracked serial after := by
  cases step with
  | @record state thread action after ledger actual =>
    refine ⟨Nat.lt_of_lt_of_le issued (advance_next ledger thread action), ?_⟩
    intro call saved active origin found
    cases actual with
    | invoke idle admitted =>
      by_cases same : tracked = thread
      · subst thread
        simp only [advance, bind, ↓reduceIte, Option.some.injEq] at active
        subst call
        simp only at origin
        change serial < ledger.next at issued
        omega
      · exact ready call saved
          (by simpa only [advance, bind, if_neg same] using active) origin
          (by simpa only [Concurrent.update, if_neg same] using found)
    | execute executed =>
      cases executed with
      | run selected executed =>
        by_cases same : tracked = thread
        · subst thread
          simp only [Concurrent.update, ↓reduceIte, Option.some.injEq] at found
          subst saved
          exact heapStable _ (preserves _ _ _ (heapStable _ (ready call _ active origin selected) _) executed) _
        · exact ready call saved active origin (by simpa only [Concurrent.update, if_neg same] using found)
    | complete halted =>
      by_cases same : tracked = thread
      · subst thread
        simp [advance, bind] at active
      · exact ready call saved (by simpa only [advance, bind, if_neg same] using active) origin
          (by simpa only [Host.retire, if_neg same] using found)
    | memory => exact ready call saved active origin found

theorem selected_history (program : Events.Program E) (policy : Host.Policy)
    (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (Concurrent.withHeap state heap))
    (preserves : ∀ before events after, P before → Events.Step program before events after → P after)
    (issued : serial < before.ledger.next) (ready : Selected P tracked serial before)
    (path : Transition.Events.Reaches (Step program policy) before ticks after) :
    serial < after.ledger.next ∧ Selected P tracked serial after := by
  induction path with
  | refl => exact ⟨issued, ready⟩
  | next first rest ih =>
    obtain ⟨issued, ready⟩ := selected_step program policy P heapStable preserves issued ready first
    exact ih issued ready

end Rumoca.CCalls.Host.Recording
