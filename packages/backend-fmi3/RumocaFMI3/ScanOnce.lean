import RumocaFMI3.PostClaimHistory
import RumocaC.AtomicScanClaimState

namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CCallSites CAtomicScan.ConcurrentInvariant
variable [interface : CInterface] {E : Type}

/-- The actual successful exchange supplies the control state needed for
the complete remaining host history. No post-claim state annotation, helper
interval or injective event tag is supplied by the caller. -/
theorem scan_once (model : Solve.FMI3Model source) (sigs : List Signature)
    (program : Events.Program E) (actual : program.internal = LiteralPreparation.program model sigs)
    (onlyNamed : ∀ name, ReservationOrigin.allowed name = false → NamedOnly program name)
    (policy : Host.Policy) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (range : count < 2^64)
    (ready : FullReady flags count (.caller (.declare "size_t" "slot")
      (StaticFactory.guard :: StaticFactory.initializeInstance model.solve kind) env types "fmi3Instance" .done)
      (.calling "atomic_exchange" args oldHeap later))
    (calling : current.threads tracked = some (.calling "atomic_exchange" args oldHeap later))
    (step : Concurrent.Step program current tracked events after)
    (active : ledger.active tracked = some call) (issued : call.serial < ledger.next) :
    ∃ k : Nat, ∃ observed : Bool, ∃ nextHeap : Heap,
      k < count ∧ args = [.pointer (some (flags.index k)), CAtomicBoolean.value true] ∧
      CAtomicBoolean.exchange current.heap (flags.index k) true = some (observed, nextHeap) ∧
      events = [tag (.exchange (flags.index k) observed true)] ∧ after.heap = nextHeap ∧
      (observed = false → ∀ ticks finish,
        Transition.Events.Reaches (Host.Recording.Step program policy) ⟨after, ledger⟩ ticks finish →
        ∀ laterCall name values heap stack,
          finish.ledger.active tracked = some laterCall → laterCall.serial = call.serial →
          finish.runtime.threads tracked = some (.calling name values heap stack) →
          ReservationOrigin.allowed name = true) := by
  obtain ⟨k, observed, nextHeap, bounded, arguments, operation, trace, heap, successful⟩ :=
    scan_claim_state program tag boolean pointer bound ready calling step
  refine ⟨k, observed, nextHeap, bounded, arguments, operation, trace, heap, ?_⟩
  intro success ticks finish path
  exact post_claim_history model sigs program actual onlyNamed policy size (Nat.lt_trans bounded range)
    active issued (successful success) path

end Rumoca.FMI3.ConcurrentSlots
