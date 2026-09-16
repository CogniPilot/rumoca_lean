import RumocaFMI3.PublicationHistory

namespace Rumoca.FMI3.PublicationRegistry
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type}

/-- Reuse the existing actual-C flag proof through the exact registry
projection. Publication introduces no new atomic or shared-memory semantics. -/
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
      ReservationRegistry.Ready flags capacity current)
    {before after : Configuration capacity}
    (prior : Transition.Events.Reaches (Host.Recording.Step program policy) initial trace before.recorded)
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after)
    (represented : SlotOwners.Represents flags before.recorded.runtime.heap (reservations before.publications)) :
    SlotOwners.Represents flags after.recorded.runtime.heap (reservations after.publications) := by
  exact ReservationRegistry.history_represents program policy tag boolean pointer exchangeBound clearBound
    foreign memory initial reachable prior (history_reservations path) represented

omit interface in
theorem published_reservation (published : Published state slot lease) : reservations state slot = some lease := by
  change state slot = some ⟨lease, true⟩ at published
  simp [reservations, published]

/-- The same history accounts for current physical flags and gives an actual
observed factory return behind each current publication. This is bookkeeping,
not yet a proof that a caller possesses authority to use that handle. -/
theorem history_checked (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (exchangeBound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (clearBound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (foreign : CStoreInvariant.ExceptPreserves CAtomicBoolean.Preserves AtomicFlagFrame.AtomicRoutine program)
    (memory : ∀ state thread heap, policy.memory state thread heap → CAtomicBoolean.Preserves state.heap heap)
    (initial : Host.Recording.State)
    (reachable : ∀ trace current, Transition.Events.Reaches (Host.Recording.Step program policy) initial trace current →
      ReservationRegistry.Ready flags capacity current)
    {after : Configuration capacity}
    (path : Transition.Events.Reaches (Step program policy instances flags)
      ⟨initial, fun _ => none⟩ ticks after)
    (represented : SlotOwners.Represents flags initial.runtime.heap (fun _ : Fin capacity => none)) :
    Host.History program policy initial.runtime (Host.Recording.erase ticks) after.recorded.runtime ∧
    SlotOwners.Represents flags after.recorded.runtime.heap (reservations after.publications) ∧
    (∀ slot lease, Published after.publications slot lease →
      ∃ tick ∈ ticks, Observed instances slot lease tick) := by
  refine ⟨Host.Recording.history_erases (history_erases path),
    history_represents (instances := instances) (before := ⟨initial, fun _ => none⟩) (after := after)
      (trace := []) program policy tag boolean pointer exchangeBound clearBound foreign memory
      initial reachable (.refl _) path represented, ?_⟩
  intro slot lease published
  rcases history_publication_origin path published with impossible | found
  · cases impossible
  · exact found

end Rumoca.FMI3.PublicationRegistry
