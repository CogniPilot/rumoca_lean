import RumocaFMI3.ConcurrentSlotCalls
import RumocaC.InvocationLedger
import RumocaC.AtomicScanClaimHistory

namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CAtomicBoolean CAtomicScan.ConcurrentInvariant
open CCalls.Concurrent (BeforeReturn IntervalStep ownTrace)
variable [interface : CInterface] {capacity : Nat} {E : Type}
variable {owners : SlotOwners.State capacity}

/-- Actual reservation result, its matching invocation record, and the
successful scan continuation. Ownership is asserted at the atomic result;
future heap/lease preservation is not hidden in the control-only suffix. -/
def ScanClaimOutcome (program : Events.Program E) (policy : Host.Policy) (tag : Calls.Event → E)
    (block : Nat) (current : Concurrent.State) (ledger : Host.Recording.Ledger)
    (owners : SlotOwners.State capacity) (tracked : Nat) (call : Host.Recording.Invocation)
    (stack : Typed.Continuation) (args : List Value) (events : List E) (after : Concurrent.State) : Prop :=
    ∃ slot : Fin capacity, ∃ observed : Bool, ∃ next : SlotOwners.State capacity,
      args = [.pointer (some (AtomicSlots.address block slot)), value true] ∧
      events = [tag (.exchange (AtomicSlots.address block slot) observed true)] ∧
      Claim owners slot call.serial observed next ∧ SlotOwners.Represents block after.heap next ∧
      Host.Recording.Step program policy ⟨current, ledger⟩
        [⟨tracked, .execute events, some call⟩] ⟨after, ledger⟩ ∧
      (observed = false → next slot = some call.serial ∧
        ∀ ticks finish, Transition.Events.Reaches (IntervalStep program tracked stack) after ticks finish →
          ownTrace tracked ticks = [] ∧
          (∀ name args heap later, finish.threads tracked = some (.calling name args heap later) → False) ∧
          (∀ result heap, finish.threads tracked = some (.returning result heap stack) → result = .integer slot.val))

/-- A reached helper exchange derives its slot from its original pool, uses
its enclosing invocation serial as lease, and retains the successful index
through all subsequent interleavings before return. Current flag representation
and helper-entry provenance remain explicit; publication is a later phase. -/
theorem scan_claim_outcome (program : Events.Program E) (policy : Host.Policy) (tag : Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions CAtomicScan.function.signature.name = some (.tree CAtomicScan.function))
    (range : capacity < 2 ^ 64)
    (entry : before.threads tracked = some
      (.calling CAtomicScan.function.signature.name [.pointer (some ⟨block, [], 0⟩), .integer capacity] savedHeap stack))
    (priorSteps : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen) before current)
    (calling : current.threads tracked = some (.calling "atomic_exchange" args oldHeap later))
    (actual : Concurrent.Step program current tracked events after)
    (active : ledger.active tracked = some call)
    (represented : SlotOwners.Represents block current.heap owners) :
    ScanClaimOutcome program policy tag block current ledger owners tracked call stack args events after := by
  obtain ⟨k, observed, nextHeap, bounded, arguments, operation, trace, heapSame, successful⟩ :=
    scan_claim_step program tag boolean pointer size constantSize named bound defined range entry priorSteps calling actual
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
