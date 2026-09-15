import RumocaFMI3.ReservationClaims
import RumocaC.InvocationLedger

namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CAtomicBoolean
variable [interface : CInterface] {capacity : Nat} {E : Type}
variable {owners : SlotOwners.State capacity}

/-- One actual exchange, recorded using its enclosing invocation's serial.
The record and slot lease refer to the same execution, not two separately
assumed traces. A failed exchange retains the existing slot owner. -/
def RecordedClaim (program : Events.Program E) (policy : Host.Policy)
    (tag : Calls.Event → E) (block : Nat) (before : Concurrent.State)
    (ledger : Host.Recording.Ledger) (owners : SlotOwners.State capacity)
    (thread : Nat) (call : Host.Recording.Invocation) : Prop :=
  ∃ slot : Fin capacity, ∃ after : Concurrent.State,
    let busy := (SlotOwners.occupied owners) slot
    let next := claimOwners owners slot call.serial
    let effects := [tag (.exchange (AtomicSlots.address block slot) busy true)]
    Claim owners slot call.serial busy next ∧
    SlotOwners.Represents block after.heap next ∧
    (∀ events target, Concurrent.Step program before thread events target ↔ events = effects ∧ target = after) ∧
    ScheduledStep program block ⟨before, owners⟩
      [⟨thread, effects, some (.claim slot call.serial busy)⟩] ⟨after, next⟩ ∧
    Host.Recording.Step program policy ⟨before, ledger⟩
      [⟨thread, .execute effects, some call⟩] ⟨after, ledger⟩ ∧
    (∀ other, other ≠ thread → after.threads other = before.threads other)

/-- Origin comes from the computed active ledger. The unique actual exchange
supplies both the ownership step and the recorded C step with that serial. -/
theorem recorded_claim (program : Events.Program E) (policy : Host.Policy) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (Calls.exchangeExternal tag boolean))
    (active : ledger.active thread = some call)
    (bounded : ∀ args heap stack,
      before.threads thread = some (.calling "atomic_exchange" args heap stack) →
      ∃ slot : Fin capacity, args = [.pointer (some (AtomicSlots.address block slot)), value true])
    (calling : before.threads thread = some (.calling "atomic_exchange" args savedHeap stack))
    (represented : SlotOwners.Represents block before.heap owners) :
    RecordedClaim program policy tag block before ledger owners thread call := by
  obtain ⟨slot, after, unique, claim, memory, scheduled, _, others⟩ :=
    bounded_reservation_claim program tag boolean pointer bound bounded calling represented call.serial
  refine ⟨slot, after, claim, memory, unique, scheduled, ?_, others⟩
  have actual := (unique _ _).mpr ⟨rfl, rfl⟩
  simpa only [Host.Recording.stamp, Host.Recording.origin, active, Host.Recording.advance] using
    (Host.Recording.Step.record (ledger := ledger) (Host.Step.execute (policy := policy) actual))

end Rumoca.FMI3.ConcurrentSlots
