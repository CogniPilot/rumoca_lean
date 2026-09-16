import RumocaFMI3.InstanceAuthorityActions
import RumocaFMI3.InitializedPublication

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CBody CCalls CCalls.Host.Recording
open CAtomicScan.ConcurrentInvariant StaticFactory
variable [interface : CInterface] {E : Type}

/-- Successful actual initialization and host completion issue the current
importer resource for the initialized instance. The same derived return and
publication are used throughout. A private-value frame and retained private
reservation remain explicit obligations of the complete caller protocol. -/
theorem initialized_handle (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (instances : Nat) (flags : Address) (slot : Fin capacity) (tracked : Nat)
    (environment logger : Option Address) (logging : Bool)
    (before : Host.Recording.State) (finish : PublicationRegistry.Configuration capacity)
    (authority : State capacity) (linked : Linked authority finish.publications)
    (call : Invocation) (saved : Typed.State)
    (scope : StaticFactory.Scope env ⟨instances, [], 0⟩ flags capacity environment logger logging)
    (storage : InstanceSlot.Storage before.runtime.heap (AtomicSlots.address instances slot))
    (bounded : slot.val < 2^64)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handleType : interface.types "fmi3Instance" = some .pointer)
    (fresh : Fresh before.ledger) (active : before.ledger.active tracked = some call)
    (factory : ReservationOrigin.factory call.name)
    (found : before.runtime.threads tracked = some saved)
    (control : ClaimedReady flags capacity slot.val (ClaimInitialization.caller model kind env types) saved)
    (path : Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        InterferenceFrame {q | (AtomicSlots.address instances slot).InRecord q} tracked call.serial a ticks b)
      before ticks finish.recorded)
    (stillActive : finish.recorded.ledger.active tracked = some call)
    (privateEntry : finish.publications slot = some ⟨call.serial, false⟩)
    (completed : Host.Step program policy finish.recorded.runtime tracked (.complete value) following)
    (flagBlock : Nat) :
    value = Handle.value instances ⟨slot, call.serial⟩ ∧
    InstanceInitialization.Initialized following.heap (AtomicSlots.address instances slot) kind environment logger logging ∧
    InstanceSlot.Storage following.heap (AtomicSlots.address instances slot) ∧
    load following.heap ((AtomicSlots.address instances slot).member "slot") = some (.integer slot.val) ∧
    ∃ nextAuthority nextPublications,
      publish authority ⟨slot, call.serial⟩ = some nextAuthority ∧
      Owns nextAuthority ⟨slot, call.serial⟩ ∧ Linked nextAuthority nextPublications ∧
      PublicationRegistry.Published nextPublications slot call.serial ∧
      PublicationRegistry.Step program policy instances flagBlock finish
        [stamp finish.recorded.ledger tracked (.complete value)]
        ⟨⟨following, Host.Recording.advance (E := E) finish.recorded.ledger tracked (.complete value)⟩, nextPublications⟩ := by
  obtain ⟨returned, initialized, writable, metadata, _⟩ :=
    PublicationRegistry.claimed_publication program policy model kind env types instances flags slot tracked
      environment logger logging before finish call saved scope storage bounded size pointer double handleType fresh active
      factory found control path stillActive privateEntry completed flagBlock
  obtain ⟨nextAuthority, issued, owned, related, published, _, actual⟩ :=
    factory_complete program policy finish authority instances flagBlock tracked slot call linked stillActive factory privateEntry
      (by simpa only [returned] using completed)
  exact ⟨returned, initialized, writable, metadata, nextAuthority, _, issued, owned, related, published,
    by simpa only [returned, Handle.value] using actual⟩

end Rumoca.FMI3.InstanceAuthority
