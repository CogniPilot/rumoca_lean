import RumocaFMI3.PublicationHistory
import RumocaFMI3.PublicationTransitions
import RumocaFMI3.ClaimInitializationHistory

namespace Rumoca.FMI3.PublicationRegistry
open CTree CMemory CBody CCalls CCalls.Host.Recording
open CAtomicScan.ConcurrentInvariant StaticFactory
variable [interface : CInterface] {E : Type}

/-- The same actual factory completion both returns an initialized record and
publishes its retained reservation. Typed initial storage, private-region
interference and retention of this lease remain explicit lifetime obligations;
no initialized result, successful initializer run or next publication map is
provided by the caller. -/
theorem claimed_publication (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (instances : Nat) (flags : Address) (slot : Fin capacity) (tracked : Nat)
    (environment logger : Option Address) (logging : Bool)
    (before : Host.Recording.State) (finish : Configuration capacity)
    (call : Invocation) (saved : Typed.State)
    (scope : StaticFactory.Scope env ⟨instances, [], 0⟩ flags capacity environment logger logging)
    (storage : InstanceSlot.Storage before.runtime.heap (AtomicSlots.address instances slot))
    (bounded : slot.val < 2^64)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (fresh : Fresh before.ledger) (active : before.ledger.active tracked = some call)
    (factory : ReservationOrigin.factory call.name)
    (found : before.runtime.threads tracked = some saved)
    (control : ClaimedReady flags capacity slot.val (ClaimInitialization.caller model kind env types) saved)
    (path : Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        InterferenceFrame {q | (AtomicSlots.address instances slot).InRecord q} tracked call.serial a ticks b)
      before ticks finish.recorded)
    (stillActive : finish.recorded.ledger.active tracked = some call)
    (owned : finish.publications slot = some ⟨call.serial, previous⟩)
    (completed : Host.Step program policy finish.recorded.runtime tracked (.complete value) following)
    (flagBlock : Nat) :
    value = .pointer (some (AtomicSlots.address instances slot)) ∧
    InstanceInitialization.Initialized following.heap (AtomicSlots.address instances slot) kind environment logger logging ∧
    InstanceSlot.Storage following.heap (AtomicSlots.address instances slot) ∧
    load following.heap ((AtomicSlots.address instances slot).member "slot") = some (.integer slot.val) ∧
    ∃ nextPublications,
      Step program policy instances flagBlock finish
        [stamp finish.recorded.ledger tracked (.complete value)]
        ⟨⟨following, Host.Recording.advance (E := E) finish.recorded.ledger tracked (.complete value)⟩, nextPublications⟩ ∧
      Published nextPublications slot call.serial ∧
      reservations nextPublications = reservations finish.publications := by
  have address : (Address.mk instances [] 0).index slot.val = AtomicSlots.address instances slot := by
    simp [Address.index, AtomicSlots.address]
  obtain ⟨returned, initialized, writable, metadata, _⟩ :=
    ClaimInitialization.claimed_observed program policy model kind env types ⟨instances, [], 0⟩ flags
      capacity slot.val tracked environment logger logging before finish.recorded call saved scope
      (by simpa only [address] using storage) slot.isLt bounded size pointer double handle fresh active found control
      (by simpa only [address] using path) stillActive completed
  rw [address] at returned initialized writable metadata
  refine ⟨returned, initialized, writable, metadata,
    advance finish.publications instances flagBlock finish.recorded tracked (.complete value), .record completed, ?_, ?_⟩
  · rw [returned]
    exact observe_owned stillActive factory owned
  · exact reservations_observe _ _ _ _ _

end Rumoca.FMI3.PublicationRegistry
