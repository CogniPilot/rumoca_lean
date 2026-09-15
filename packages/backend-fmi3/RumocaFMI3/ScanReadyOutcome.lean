import RumocaFMI3.ScanClaimOutcome
import RumocaC.AtomicScanClaimState

namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CAtomicBoolean CAtomicScan.ConcurrentInvariant
variable [interface : CInterface] {capacity : Nat} {E : Type}
variable {owners : SlotOwners.State capacity}

/-- The actual public-entry invariant can discharge scan provenance without
an independently supplied helper interval. Current owner/flag representation
remains an explicit memory obligation. -/
theorem scan_ready_outcome (program : Events.Program E) (policy : Host.Policy) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (bound : program.externals "atomic_exchange" = some (Calls.exchangeExternal tag boolean))
    (range : capacity < 2 ^ 64)
    (ready : FullReady ⟨block, [], 0⟩ capacity stack (.calling "atomic_exchange" args oldHeap later))
    (calling : current.threads tracked = some (.calling "atomic_exchange" args oldHeap later))
    (actual : Concurrent.Step program current tracked events after)
    (active : ledger.active tracked = some call)
    (represented : SlotOwners.Represents block current.heap owners) :
    ScanClaimOutcome program policy tag block current ledger owners tracked call stack args events after := by
  obtain ⟨k, observed, nextHeap, bounded, arguments, operation, trace, heapSame, successful⟩ :=
    scan_claim_state program tag boolean pointer bound ready calling actual
  let slot : Fin capacity := ⟨k, bounded⟩
  have address : (Address.mk block [] 0).index k = AtomicSlots.address block slot := by
    simp [Address.index, AtomicSlots.address, slot]
  rw [address] at arguments operation trace
  obtain ⟨reservedHeap, next, reservation, claim, memory⟩ := reserve_operation represented slot call.serial
  obtain ⟨observedSame, targetSame⟩ := Prod.mk.inj (Option.some.inj (operation.symm.trans reservation))
  rw [← observedSame] at claim
  refine ⟨slot, observed, next, arguments, trace, claim, ?_, ?_, ?_⟩
  · simpa only [heapSame, targetSame] using memory
  · simpa only [Host.Recording.stamp, Host.Recording.origin, active, Host.Recording.advance] using
      (Host.Recording.Step.record (ledger := ledger) (Host.Step.execute (policy := policy) actual))
  · intro success
    have owned : next slot = some call.serial := (claim_success (by simpa only [success] using claim)).2.1
    refine ⟨owned, ?_⟩
    intro ticks finish path
    exact claimed_interval program size (Nat.lt_trans bounded range) (successful success) path

end Rumoca.FMI3.ConcurrentSlots
