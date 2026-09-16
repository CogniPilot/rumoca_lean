import RumocaC.WriteRegions
import RumocaC.InvocationRegion

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory
variable [CInterface] {E : Type}

/-- Obligations on current controls and the explicit host-memory policy while
the original invocation is active. Internal C effects are computed from their
destinations; no resulting internal heap frame is assumed. -/
def InterferenceControls (region : Set Address) (program : Events.Program E)
    (policy : Host.Policy) (tracked serial : Nat) (before : State) : Prop :=
  (∃ call, before.ledger.active tracked = some call ∧ call.serial = serial) →
    (∀ thread, thread ≠ tracked → ∀ saved, before.runtime.threads thread = some saved →
      CWriteFootprint.Avoids region (Concurrent.withHeap saved before.runtime.heap) ∧
      CWriteFootprint.ForeignFrame region program (Concurrent.withHeap saved before.runtime.heap)) ∧
    (∀ thread heap, before.runtime.threads thread = none →
      policy.memory before.runtime thread heap → Set.EqOn before.runtime.heap heap region)

/-- Derive interference from the actual selected C transition or admitted
host-memory action. Invocation and observation do not touch memory. -/
theorem controls_frame
    (controls : InterferenceControls region program policy tracked serial before)
    (step : Step program policy before ticks after) :
    InterferenceFrame region tracked serial before ticks after := by
  cases step with
  | record actual =>
    intro active tick member
    obtain ⟨methods, memory⟩ := controls active
    have same := List.mem_singleton.mp member
    subst tick
    cases actual with
    | invoke => trivial
    | complete => trivial
    | execute executed =>
      intro different
      exact CWriteFootprint.concurrent_region
        (fun saved found => (methods _ different saved found).1)
        (fun saved found => (methods _ different saved found).2) executed
    | memory idle allowed => exact memory _ _ idle allowed

/-- The controlled and framed paths describe exactly the same recorded
actions. All internal-step heap frames follow from current destinations. -/
theorem controls_history
    (path : Transition.Events.Reaches
      (fun a ticks b => Step program policy a ticks b ∧
        InterferenceControls region program policy tracked serial a)
      before ticks after) :
    Transition.Events.Reaches
      (fun a ticks b => Step program policy a ticks b ∧
        InterferenceFrame region tracked serial a ticks b)
      before ticks after := by
  induction path with
  | refl => exact .refl _
  | next first rest ih => exact .next ⟨first.1, controls_frame first.2 first.1⟩ ih

end Rumoca.CCalls.Host.Recording

namespace Rumoca.CWriteFootprint
open CMemory CCalls
variable [CInterface]

theorem ForeignFrame.mono (frame : ForeignFrame larger program state)
    (included : smaller ⊆ larger) : ForeignFrame smaller program state := by
  cases state with
  | calling name args before stack =>
    intro fn values events result after found converted executed query inside
    exact frame fn values events result after found converted executed (included inside)
  | body | kernel | returning | halted => trivial

end Rumoca.CWriteFootprint

namespace Rumoca.CWriteFootprint
open CMemory CCalls
variable [CInterface]

/-- A call to an actual internal definition cannot select a foreign effect.
This supplies every region frame at public entry without assuming a callback. -/
theorem internal_entry_foreign_frame (defined : program.internal.definitions name = some fn) :
    ForeignFrame region program (.calling name args heap stack) := by
  intro foreign values events result after found _ _
  have absent := program.disjoint name foreign found
  rw [defined] at absent
  contradiction

end Rumoca.CWriteFootprint
