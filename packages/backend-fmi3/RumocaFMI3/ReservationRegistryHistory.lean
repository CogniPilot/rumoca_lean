import RumocaFMI3.ReservationRegistryExecution

noncomputable section
namespace Rumoca.FMI3.ReservationRegistry
open CTree CMemory CCalls
variable {capacity : Nat}

def advance (owners : SlotOwners.State capacity) (block : Nat)
    (state : Host.Recording.State) (thread : Nat) : Host.Action E → SlotOwners.State capacity
  | .execute _ => executeUpdate owners block state thread
  | .invoke _ _ | .complete _ | .memory => owners

structure Configuration (capacity : Nat) where
  recorded : Host.Recording.State
  reservations : SlotOwners.State capacity

/-- Add a deterministically computed reservation map to actual host steps.
There are no supplied slot, lease, observation or next-map annotations. -/
inductive Step [CInterface] (program : Events.Program E) (policy : Host.Policy) (block : Nat) :
    Configuration capacity → List (Host.Recording.Tick E) → Configuration capacity → Prop where
  | record (actual : Host.Step program policy before thread action after) :
      Step program policy block ⟨⟨before, ledger⟩, owners⟩ [Host.Recording.stamp ledger thread action]
        ⟨⟨after, Host.Recording.advance ledger thread action⟩,
          advance owners block ⟨before, ledger⟩ thread action⟩

variable [interface : CInterface] {E : Type}

theorem Step.erases (step : Step program policy block before ticks after) :
    Host.Recording.Step program policy before.recorded ticks after.recorded := by
  cases step with
  | record actual => exact .record actual

/-- Any recorded actual history computes a reservation history, independently
of whether it satisfies the later memory or live-instance protocol. -/
theorem history_lift (program : Events.Program E) (policy : Host.Policy) (block : Nat)
    (path : Transition.Events.Reaches (Host.Recording.Step program policy) before ticks after)
    (owners : SlotOwners.State capacity) :
    ∃ following, Transition.Events.Reaches (Step program policy block)
      ⟨before, owners⟩ ticks ⟨after, following⟩ := by
  induction path generalizing owners with
  | refl => exact ⟨owners, .refl _⟩
  | next first rest ih =>
    cases first with
    | record actual =>
      obtain ⟨following, later⟩ := ih (advance owners block _ _ _)
      exact ⟨following, .next (.record actual) later⟩

theorem history_erases
    (path : Transition.Events.Reaches (Step program policy block) before ticks after) :
    Transition.Events.Reaches (Host.Recording.Step program policy) before.recorded ticks after.recorded := by
  induction path with
  | refl => exact .refl _
  | next first rest ih => exact .next first.erases ih

theorem step_represents (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (exchangeBound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (clearBound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (foreign : CStoreInvariant.ExceptPreserves CAtomicBoolean.Preserves AtomicFlagFrame.AtomicRoutine program)
    (memory : ∀ state thread heap, policy.memory state thread heap → CAtomicBoolean.Preserves state.heap heap)
    {before after : Configuration capacity}
    (ready : Ready block capacity before.recorded)
    (represented : SlotOwners.Represents block before.recorded.runtime.heap before.reservations)
    (step : Step program policy block before ticks after) :
    SlotOwners.Represents block after.recorded.runtime.heap after.reservations := by
  cases step with
  | record actual =>
    cases actual with
    | invoke | complete => exact represented
    | memory idle allowed => exact SlotOwners.ordinary_preserves represented (memory _ _ _ allowed)
    | execute executed =>
      exact execute_represents program tag boolean pointer exchangeBound clearBound foreign ready represented executed

/-- Starting from one represented heap, every subsequent representation is
derived from real steps and computed maps. Reachable operand/control facts
and importer memory frames are the explicit generic instantiation boundary. -/
theorem history_represents (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (exchangeBound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (clearBound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (foreign : CStoreInvariant.ExceptPreserves CAtomicBoolean.Preserves AtomicFlagFrame.AtomicRoutine program)
    (memory : ∀ state thread heap, policy.memory state thread heap → CAtomicBoolean.Preserves state.heap heap)
    (initial : Host.Recording.State)
    (reachable : ∀ trace current, Transition.Events.Reaches (Host.Recording.Step program policy) initial trace current →
      Ready block capacity current)
    {before after : Configuration capacity}
    (prior : Transition.Events.Reaches (Host.Recording.Step program policy) initial trace before.recorded)
    (path : Transition.Events.Reaches (Step program policy block) before ticks after)
    (represented : SlotOwners.Represents block before.recorded.runtime.heap before.reservations) :
    SlotOwners.Represents block after.recorded.runtime.heap after.reservations := by
  induction path generalizing trace with
  | refl => exact represented
  | next first rest ih =>
    exact ih (prior.trans (.next first.erases (.refl _)))
      (step_represents program policy tag boolean pointer exchangeBound clearBound foreign memory
        (reachable _ _ prior) represented first)

end Rumoca.FMI3.ReservationRegistry
