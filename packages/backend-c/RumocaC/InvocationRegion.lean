import RumocaC.InvocationContinuation
import RumocaC.MemoryFootprint

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory

/-- A heap-dependent property is evaluated with the current shared heap,
never the erased heap stored in a saved thread control. -/
def CurrentSelected (P : Typed.State → Prop) (tracked serial : Nat) (state : State) : Prop :=
  Selected (fun saved => P (Concurrent.withHeap saved state.runtime.heap)) tracked serial state

/-- Only interference while this particular invocation is still active needs
the region frame. Own C execution is proved separately; completion ends this
obligation even if the thread or storage is reused by a later invocation. -/
def InterferenceFrame (region : Set Address) (tracked serial : Nat)
    (before : State) (ticks : List (Tick E)) (after : State) : Prop :=
  (∃ call, before.ledger.active tracked = some call ∧ call.serial = serial) →
    ∀ tick ∈ ticks, match tick.action with
      | .execute _ => tick.thread ≠ tracked → Set.EqOn before.runtime.heap after.runtime.heap region
      | .memory => Set.EqOn before.runtime.heap after.runtime.heap region
      | .invoke _ _ | .complete _ => True

variable [CInterface] {E : Type}

theorem current_selected_step (program : Events.Program E) (policy : Host.Policy)
    (P : Typed.State → Prop) (region : Set Address)
    (heapFrame : ∀ state heap, P state → Set.EqOn (CReadOnly.typedHeap state) heap region →
      P (Concurrent.withHeap state heap))
    (preserves : ∀ before events after, P before → Events.Step program before events after → P after)
    (issued : serial < before.ledger.next)
    (ready : CurrentSelected P tracked serial before)
    (frame : InterferenceFrame region tracked serial before ticks after)
    (step : Step program policy before ticks after) :
    serial < after.ledger.next ∧ CurrentSelected P tracked serial after := by
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
      rename_i effects
      cases executed with
      | run selected executed =>
        by_cases same : tracked = thread
        · subst thread
          simp only [Concurrent.update, ↓reduceIte, Option.some.injEq] at found
          subst saved
          have next := preserves _ _ _ (ready call _ active origin selected) executed
          simpa only [Concurrent.control_resume, Concurrent.withHeap_original] using next
        · have previous := ready call saved active origin
            (by simpa only [Concurrent.update, if_neg same] using found)
          have stable : Set.EqOn state.heap _ region := frame ⟨call, active, origin⟩ (stamp ledger thread (.execute effects)) (by simp) (Ne.symm same)
          simpa only [Concurrent.withHeap_twice] using
            heapFrame _ _ previous (by simpa only [Concurrent.heap_withHeap] using stable)
    | complete halted =>
      by_cases same : tracked = thread
      · subst thread
        simp [advance, bind] at active
      · exact ready call saved (by simpa only [advance, bind, if_neg same] using active) origin
          (by simpa only [Host.retire, if_neg same] using found)
    | memory idle allowed =>
      have previous := ready call saved active origin found
      have stable : Set.EqOn state.heap _ region := frame ⟨call, active, origin⟩ (stamp ledger thread .memory) (by simp)
      simpa only [Concurrent.withHeap_twice] using
        heapFrame _ _ previous (by simpa only [Concurrent.heap_withHeap] using stable)

/-- Lift the heap-dependent invariant across actual host actions with an
explicit interference contract, and return their unchanged recording history.
Proving that legal callers establish the frame remains an instantiation duty. -/
theorem current_selected_history (program : Events.Program E) (policy : Host.Policy)
    (P : Typed.State → Prop) (region : Set Address)
    (heapFrame : ∀ state heap, P state → Set.EqOn (CReadOnly.typedHeap state) heap region →
      P (Concurrent.withHeap state heap))
    (preserves : ∀ before events after, P before → Events.Step program before events after → P after)
    (issued : serial < before.ledger.next) (ready : CurrentSelected P tracked serial before)
    (path : Transition.Events.Reaches
      (fun a ticks b => Step program policy a ticks b ∧ InterferenceFrame region tracked serial a ticks b)
      before ticks after) :
    serial < after.ledger.next ∧ CurrentSelected P tracked serial after ∧
      Transition.Events.Reaches (Step program policy) before ticks after := by
  induction path with
  | refl => exact ⟨issued, ready, .refl _⟩
  | next first rest ih =>
    obtain ⟨nextIssued, nextReady⟩ := current_selected_step program policy P region heapFrame preserves
      issued ready first.2 first.1
    obtain ⟨lastIssued, lastReady, actual⟩ := ih nextIssued nextReady
    exact ⟨lastIssued, lastReady, .next first.1 actual⟩

end Rumoca.CCalls.Host.Recording
