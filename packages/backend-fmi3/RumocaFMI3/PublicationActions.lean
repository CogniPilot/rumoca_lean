import RumocaFMI3.PublicationState
import RumocaFMI3.ReservationRegistryHistory
import RumocaFMI3.ReservationOriginPolicy

namespace Rumoca.FMI3.PublicationRegistry
open CMemory CCalls

private local instance factoryDecidable (name : String) : Decidable (ReservationOrigin.factory name) :=
  inferInstanceAs (Decidable (name = "fmi3InstantiateModelExchange" ∨ name = "fmi3InstantiateCoSimulation"))

/-- Only a factory's observed nonnull return can publish its own current
reservation. The instance decoder is exact and bounded. -/
def observe (state : State capacity) (instances : Nat) (ledger : Host.Recording.Ledger)
    (thread : Nat) (value : Value) : State capacity :=
  match value with
  | .pointer (some address) => match ledger.active thread with
    | some call => if ReservationOrigin.factory call.name then
        match ReservationRegistry.slotAt instances capacity address with
        | some slot => publish state slot call.serial
        | none => state
      else state
    | none => state
  | _ => state

/-- Reuse the existing registry's actual-control/operand update. No second
atomic model or guessed event decoder supplies a reservation transition. -/
def advance (state : State capacity) (instances flags : Nat)
    (before : Host.Recording.State) (thread : Nat) (action : Host.Action E) : State capacity :=
  match action with
  | .execute _ => synchronize state (ReservationRegistry.executeUpdate (reservations state) flags before thread)
  | .complete value => observe state instances before.ledger thread value
  | .invoke _ _ | .memory => state

theorem reservations_observe (state : State capacity) (instances : Nat) (ledger : Host.Recording.Ledger)
    (thread : Nat) (value : Value) :
    reservations (observe state instances ledger thread value) = reservations state := by
  unfold observe
  split
  next address =>
    split
    next call active =>
      split
      next =>
        split
        next slot decoded => exact reservations_publish state slot call.serial
        next => rfl
      next => rfl
    next => rfl
  next => rfl

theorem reservations_advance (state : State capacity) (instances flags : Nat)
    (before : Host.Recording.State) (thread : Nat) (action : Host.Action E) :
    reservations (advance state instances flags before thread action) =
      ReservationRegistry.advance (reservations state) flags before thread action := by
  cases action with
  | execute events => exact reservations_synchronize _ _
  | complete value => exact reservations_observe state instances before.ledger thread value
  | invoke | memory => rfl

/-- Publication provenance is a real factory completion with its recorded
serial and the exact returned address, never a supplied later owner annotation. -/
theorem observe_origin (published : Published (observe state instances ledger thread value) slot lease) :
    Published state slot lease ∨
      ∃ call, ledger.active thread = some call ∧ call.serial = lease ∧ ReservationOrigin.factory call.name ∧
        value = .pointer (some (AtomicSlots.address instances slot)) ∧ reservations state slot = some lease := by
  unfold observe at published
  split at published
  next =>
    split at published
    next call active =>
      split at published
      next factory =>
        split at published
        next selected decoded =>
          rcases publish_origin published with old | ⟨rfl, identity, owned⟩
          · exact .inl old
          · exact .inr ⟨call, active, identity.symm, factory,
              by simp_all only [ReservationRegistry.slotAt_sound decoded], owned⟩
        next => exact .inl published
      next => exact .inl published
    next => exact .inl published
  next => exact .inl published

theorem advance_origin (published : Published (advance state instances flags before thread action) slot lease) :
    Published state slot lease ∨
      ∃ call, before.ledger.active thread = some call ∧ call.serial = lease ∧ ReservationOrigin.factory call.name ∧
        action = .complete (.pointer (some (AtomicSlots.address instances slot))) ∧
        reservations state slot = some lease := by
  cases action with
  | execute events => exact .inl (synchronize_published published)
  | complete value =>
    rcases observe_origin (instances := instances) (ledger := before.ledger) (thread := thread) (value := value) published with old | ⟨call, active, serial, factory, rfl, owned⟩
    · exact .inl old
    · exact .inr ⟨call, active, serial, factory, rfl, owned⟩
  | invoke | memory => exact .inl published

end Rumoca.FMI3.PublicationRegistry
