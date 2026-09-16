import RumocaFMI3.ClaimInitializationHistory
import RumocaC.AtomicScanClaimState

namespace Rumoca.FMI3.StaticFactory.ClaimInitialization
open CTree CMemory CBody CCalls CCalls.Host.Recording
open CAtomicScan.ConcurrentInvariant
variable [interface : CInterface] {E : Type}

/-- Actual atomic observation and its successful initialization/host-return
consequence. Typed storage and interference assumptions belong to the theorem
that establishes this outcome; it contains no supplied initializer entry. -/
def Outcome (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E) (kind : Kind)
    (base flags : Address) (capacity tracked : Nat)
    (environment logger : Option Address) (logging : Bool)
    (current : Concurrent.State) (ledger : Ledger) (call : Invocation)
    (args : List Value) (events : List E) (after : Concurrent.State) : Prop :=
    ∃ slot : Fin capacity, ∃ busy : Bool, ∃ nextHeap : Heap,
      args = [.pointer (some (flags.index slot.val)), CAtomicBoolean.value true] ∧
      CAtomicBoolean.exchange current.heap (flags.index slot.val) true = some (busy, nextHeap) ∧
      events = [tag (.exchange (flags.index slot.val) busy true)] ∧ after.heap = nextHeap ∧
      (busy = false → ∀ future finish,
        Transition.Events.Reaches
          (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
            InterferenceFrame {q | (base.index slot.val).InRecord q} tracked call.serial a ticks b)
          ⟨after, ledger⟩ future finish →
        finish.ledger.active tracked = some call →
        ∀ value following, Host.Step program policy finish.runtime tracked (.complete value) following →
          value = .pointer (some (base.index slot.val)) ∧
          InstanceInitialization.Initialized following.heap (base.index slot.val) kind environment logger logging ∧
          InstanceSlot.Storage following.heap (base.index slot.val) ∧
          load following.heap ((base.index slot.val).member "slot") = some (.integer slot.val) ∧
          Host.History program policy after (erase future ++ [(tracked, .complete value)]) following)

/-- The actual exchange supplies the slot, observation and continuation.
On success, any protected continuation that the host completes returns that
initialized slot. Neither a successful operation nor initializer entry is
supplied as a premise; typed storage survives the actual atomic operation. -/
theorem exchange_initialization (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (base flags : Address) (capacity tracked : Nat)
    (environment logger : Option Address) (logging : Bool)
    (current : Concurrent.State) (ledger : Ledger) (call : Invocation)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : ∀ slot : Fin capacity, InstanceSlot.Storage current.heap (base.index slot.val))
    (range : capacity < 2^64)
    (boolean : interface.types "_Bool" = some .boolean)
    (atomicPointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (fresh : Fresh ledger) (active : ledger.active tracked = some call)
    (ready : FullReady flags capacity (caller model kind env types) (.calling "atomic_exchange" args oldHeap later))
    (calling : current.threads tracked = some (.calling "atomic_exchange" args oldHeap later))
    (actual : Concurrent.Step program current tracked events after) :
    Outcome program policy tag kind base flags capacity tracked environment logger logging current ledger call args events after := by
  obtain ⟨k, busy, nextHeap, inside, arguments, operation, trace, heapSame, success⟩ :=
    scan_claim_state program tag boolean atomicPointer bound ready calling actual
  let slot : Fin capacity := ⟨k, inside⟩
  refine ⟨slot, busy, nextHeap, arguments, operation, trace, heapSame, ?_⟩
  intro vacant future finish path stillActive value following completed
  obtain ⟨saved, found, control⟩ := success vacant
  have available : InstanceSlot.Storage after.heap (base.index k) := by
    rw [heapSame]
    exact (storage slot).preserved (CAtomicBoolean.exchange_storage operation)
  exact claimed_observed program policy model kind env types base flags capacity k tracked environment logger logging
    ⟨after, ledger⟩ finish call saved scope available inside (Nat.lt_trans inside range)
    size pointer double handle fresh active found control path stillActive completed

end Rumoca.FMI3.StaticFactory.ClaimInitialization
