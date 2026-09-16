import RumocaFMI3.PublicationActions

namespace Rumoca.FMI3.PublicationRegistry
open CMemory CCalls

theorem synchronize_clear (state : State capacity) (slot : Fin capacity) :
    synchronize state (SlotOwners.update (reservations state) slot none) =
      fun other => if other = slot then none else state other := by
  funext other
  by_cases same : other = slot
  · subst other
    simp [synchronize, SlotOwners.update]
  · simpa only [synchronize, SlotOwners.update, if_neg same] using
      congrFun (synchronize_reservations state) other

theorem synchronize_claim_free (vacant : state slot = none) (lease : Nat) :
    synchronize state (ConcurrentSlots.claimOwners (reservations state) slot lease) =
      fun other => if other = slot then some ⟨lease, false⟩ else state other := by
  funext other
  by_cases same : other = slot
  · subst other
    simp [synchronize, ConcurrentSlots.claimOwners, SlotOwners.occupied, SlotOwners.update, reservations, vacant]
  · simpa [synchronize, ConcurrentSlots.claimOwners, SlotOwners.occupied, SlotOwners.update,
      reservations, vacant, same] using congrFun (synchronize_reservations state) other

theorem synchronize_claim_busy (owned : state slot = some entry) (lease : Nat) :
    synchronize state (ConcurrentSlots.claimOwners (reservations state) slot lease) = state := by
  simpa [ConcurrentSlots.claimOwners, SlotOwners.occupied, reservations, owned] using synchronize_reservations state

/-- A matching observed factory completion really does publish, so publication
provenance is not satisfied by an implementation that leaves every bit false. -/
theorem observe_owned (active : ledger.active thread = some call)
    (factory : ReservationOrigin.factory call.name) (owned : state slot = some ⟨call.serial, previous⟩) :
    Published (observe state instances ledger thread (.pointer (some (AtomicSlots.address instances slot))))
      slot call.serial := by
  simpa [observe, active, factory, ReservationRegistry.slotAt_address] using publish_owned owned

/-- In particular, a delayed void completion of FreeInstance cannot revoke
or publish a new reservation that reused the same storage before it returned. -/
theorem advance_void_completion (state : State capacity) (instances flags : Nat)
    (before : Host.Recording.State) (thread : Nat) :
    advance state instances flags before thread (Host.Action.complete (E := E) .void) = state := rfl

theorem advance_clear (state : State capacity) (instances flags : Nat)
    (before : Host.Recording.State) (thread : Nat) (slot : Fin capacity) (events : List E)
    (calling : before.runtime.threads thread = some (.calling "atomic_store"
      [.pointer (some (AtomicSlots.address flags slot)), CAtomicBoolean.value false] heap stack)) :
    advance state instances flags before thread (.execute events) =
      fun other => if other = slot then none else state other := by
  simpa [advance, ReservationRegistry.executeUpdate, calling, ReservationRegistry.callUpdate,
    CAtomicBoolean.value, ReservationRegistry.clearAt_slot] using synchronize_clear state slot

theorem advance_claim_free (state : State capacity) (instances flags : Nat)
    (before : Host.Recording.State) (thread : Nat) (slot : Fin capacity) (events : List E)
    (calling : before.runtime.threads thread = some (.calling "atomic_exchange"
      [.pointer (some (AtomicSlots.address flags slot)), CAtomicBoolean.value true] heap stack))
    (active : before.ledger.active thread = some call) (vacant : state slot = none) :
    advance state instances flags before thread (.execute events) =
      fun other => if other = slot then some ⟨call.serial, false⟩ else state other := by
  simpa [advance, ReservationRegistry.executeUpdate, calling, ReservationRegistry.callUpdate,
    CAtomicBoolean.value, ReservationRegistry.slotAt_address, active] using synchronize_claim_free vacant call.serial

end Rumoca.FMI3.PublicationRegistry
