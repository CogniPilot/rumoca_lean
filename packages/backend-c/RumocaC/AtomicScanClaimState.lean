import RumocaC.AtomicScanClaim

namespace Rumoca.CAtomicScan.ConcurrentInvariant
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type}

/-- An actual shared exchange consumes the independently established scan
control invariant; its successful continuation and event come from that same
step. Complete public histories may supply the invariant directly. -/
theorem scan_claim_state (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (ready : FullReady flags count stack (.calling "atomic_exchange" args oldHeap later))
    (calling : current.threads tracked = some (.calling "atomic_exchange" args oldHeap later))
    (actual : Concurrent.Step program current tracked events after) :
    ∃ k : Nat, ∃ observed : Bool, ∃ nextHeap : Heap,
      k < count ∧ args = [.pointer (some (flags.index k)), CAtomicBoolean.value true] ∧
      CAtomicBoolean.exchange current.heap (flags.index k) true = some (observed, nextHeap) ∧
      events = [tag (.exchange (flags.index k) observed true)] ∧ after.heap = nextHeap ∧
      (observed = false → ∃ saved, after.threads tracked = some saved ∧ ClaimedReady flags count k stack saved) := by
  cases actual with
  | run selected executed =>
    cases Option.some.inj (selected.symm.trans calling)
    obtain ⟨k, observed, nextHeap, bounded, arguments, operation, trace, target, claimed⟩ :=
      scan_exchange program tag boolean pointer bound (ready.withHeap current.heap) executed
    subst target
    refine ⟨k, observed, nextHeap, bounded, arguments, operation, trace, rfl, ?_⟩
    intro success
    exact ⟨_, by simp [Concurrent.update, Concurrent.control], (claimed success).withHeap (fun _ => none)⟩

end Rumoca.CAtomicScan.ConcurrentInvariant
