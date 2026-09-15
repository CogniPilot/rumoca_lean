import RumocaC.AtomicScanClaim
import RumocaC.CallIntervalTrace

namespace Rumoca.CAtomicScan.ConcurrentInvariant
open CTree CMemory CCalls
open CCalls.Concurrent (BeforeReturn IntervalStep ownTrace)
variable [interface : CInterface] {E : Type}

/-- Interleaved finite continuations after success issue no further calls or
own events and return exactly the selected index. This is a safety result;
it does not assume or claim scheduler fairness or ownership publication. -/
theorem claimed_interval (program : Events.Program E)
    (size : interface.types "size_t" = some .size) (bounded : k < 2 ^ 64)
    (ready : ∃ saved, before.threads tracked = some saved ∧ ClaimedReady flags count k stack saved)
    (path : Transition.Events.Reaches (IntervalStep program tracked stack) before ticks after) :
    ownTrace tracked ticks = [] ∧
      (∀ name args heap later, after.threads tracked = some (.calling name args heap later) → False) ∧
      (∀ value heap, after.threads tracked = some (.returning value heap stack) → value = .integer k) := by
  obtain ⟨silent, saved, found, ready⟩ := Concurrent.silent_interval_history program
    (ClaimedReady flags count k stack) (fun _ ready heap => ready.withHeap heap)
    (fun _ _ _ ready active step => claimed_step program size bounded ready active step) ready path
  refine ⟨silent, ?_, ?_⟩
  · intro name args heap later calling
    cases Option.some.inj (found.symm.trans calling)
    exact ready.no_call
  · intro value heap returning
    cases Option.some.inj (found.symm.trans returning)
    exact ready.exit_value

/-- The helper's actual entry and shared scheduler priorSteps supply its control
invariant. Its actual exchange supplies the observation and successful
continuation. There is no supplied successful-scan or later-control annotation. -/
theorem scan_claim_step (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (range : count < 2 ^ 64)
    (entry : before.threads tracked = some
      (.calling function.signature.name [.pointer (some flags), .integer count] savedHeap stack))
    (priorSteps : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen) before current)
    (calling : current.threads tracked = some (.calling "atomic_exchange" args oldHeap later))
    (actual : Concurrent.Step program current tracked events after) :
    ∃ k : Nat, ∃ observed : Bool, ∃ nextHeap : Heap,
      k < count ∧ args = [.pointer (some (flags.index k)), CAtomicBoolean.value true] ∧
      CAtomicBoolean.exchange current.heap (flags.index k) true = some (observed, nextHeap) ∧
      events = [tag (.exchange (flags.index k) observed true)] ∧ after.heap = nextHeap ∧
      (observed = false → ∃ saved, after.threads tracked = some saved ∧ ClaimedReady flags count k stack saved) := by
  obtain ⟨saved, found, ready⟩ := full_thread_reaches program tag boolean pointer size constantSize named bound
    defined range ⟨_, entry, .entry savedHeap⟩ priorSteps
  cases Option.some.inj (found.symm.trans calling)
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
