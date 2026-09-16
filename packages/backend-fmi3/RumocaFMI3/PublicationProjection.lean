import RumocaFMI3.PublicationHistory

namespace Rumoca.FMI3.PublicationRegistry
open CTree CMemory CCalls
variable [CInterface] {E : Type}

/-- Lift a particular physical reservation history, retaining its exact final
leases as well as its actual C steps. No choice of a second execution or replay
of event tags is involved. -/
theorem reservation_history_lift (program : Events.Program E) (policy : Host.Policy) (instances flags : Nat)
    {before after : ReservationRegistry.Configuration capacity}
    (path : Transition.Events.Reaches (ReservationRegistry.Step program policy flags) before ticks after)
    (publications : State capacity) (same : reservations publications = before.reservations) :
    ∃ following, Transition.Events.Reaches (Step program policy instances flags)
      ⟨before.recorded, publications⟩ ticks ⟨after.recorded, following⟩ ∧
      reservations following = after.reservations := by
  induction path generalizing publications with
  | refl => exact ⟨publications, .refl _, same⟩
  | next first rest ih =>
    cases first with
    | @record runtime thread action following ledger owners actual =>
      obtain ⟨following, later, sameAfter⟩ := ih (advance publications instances flags ⟨runtime, ledger⟩ thread action)
        (by simp only [reservations_advance, same])
      exact ⟨following, .next (.record actual) later, sameAfter⟩

end Rumoca.FMI3.PublicationRegistry
