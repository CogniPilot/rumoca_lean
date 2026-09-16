import RumocaFMI3.FramedResourceHistory
import RumocaFMI3.InitializedPublication
import RumocaFMI3.OriginBoundaries

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CBody CCalls CCalls.Host.Recording
open CAtomicScan.ConcurrentInvariant StaticFactory
variable [interface : CInterface] {E : Type}

/-- A successful claimed initializer derives its return value, initialized
record, current handle and coupled completion. Retention at the end is derived
from the same history instead of assumed. Typed starting storage and the
private-value interference frame remain explicit caller/environment boundaries. -/
theorem initialized_from_history (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (instances flags : Nat) (slot : Fin capacity) (tracked : Nat)
    (environment logger : Option Address) (logging : Bool)
    (before finish : Configuration capacity) (call : Invocation) (saved : Typed.State)
    (invariant : Invariant instances before)
    (scope : StaticFactory.Scope env ⟨instances, [], 0⟩ ⟨flags, [], 0⟩ capacity environment logger logging)
    (storage : InstanceSlot.Storage before.resources.recorded.runtime.heap (AtomicSlots.address instances slot))
    (bounded : slot.val < 2^64)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handleType : interface.types "fmi3Instance" = some .pointer)
    (active : before.resources.recorded.ledger.active tracked = some call)
    (factory : ReservationOrigin.factory call.name)
    (found : before.resources.recorded.runtime.threads tracked = some saved)
    (control : ClaimedReady ⟨flags, [], 0⟩ capacity slot.val (ClaimInitialization.caller model kind env types) saved)
    (privateEntry : before.publications slot = some ⟨call.serial, false⟩)
    (path : Transition.Events.Reaches
      (fun a ticks b => Step program policy instances flags a ticks b ∧
        InterferenceFrame {q | (AtomicSlots.address instances slot).InRecord q} tracked call.serial
          a.resources.recorded ticks b.resources.recorded)
      before ticks finish)
    (stillActive : finish.resources.recorded.ledger.active tracked = some call)
    (completed : Host.Step program policy finish.resources.recorded.runtime tracked (.complete value) following) :
    let publications := PublicationRegistry.advance (E := E) finish.publications instances flags finish.resources.recorded tracked (.complete value)
    let ledger := Host.Recording.advance (E := E) finish.resources.recorded.ledger tracked (.complete value)
    value = Handle.value instances ⟨slot, call.serial⟩ ∧
    InstanceInitialization.Initialized following.heap (AtomicSlots.address instances slot) kind environment logger logging ∧
    InstanceSlot.Storage following.heap (AtomicSlots.address instances slot) ∧
    load following.heap ((AtomicSlots.address instances slot).member "slot") = some (.integer slot.val) ∧
    ∃ nextAuthority,
      InstanceAuthority.publish finish.resources.authority ⟨slot, call.serial⟩ = some nextAuthority ∧
      Owns nextAuthority ⟨slot, call.serial⟩ ∧
      Invariant instances ⟨⟨⟨following, ledger⟩, nextAuthority⟩, publications⟩ ∧
      PublicationRegistry.Published publications slot call.serial ∧
      Step program policy instances flags finish
        [stamp finish.resources.recorded.ledger tracked (.complete value)]
        ⟨⟨⟨following, ledger⟩, nextAuthority⟩, publications⟩ := by
  obtain ⟨coupled, framed⟩ := framed_history path
  have current := (history_invariant coupled invariant).1
  have retained := history_private_reservation coupled invariant privateEntry active stillActive
  obtain ⟨returned, initialized, writable, metadata, _⟩ :=
    PublicationRegistry.claimed_publication program policy model kind env types instances ⟨flags, [], 0⟩ slot tracked
      environment logger logging before.resources.recorded finish.published call saved scope storage bounded
      size pointer double handleType invariant.fresh active factory found control framed stillActive retained completed flags
  have boundary : FactoryResult finish.publications finish.resources.recorded tracked instances
      (Host.Action.complete (E := E) value) := FactoryResult.returned stillActive retained returned
  obtain ⟨nextAuthority, issued, owned, linked, origins, published, _⟩ :=
    factory_complete_origins program policy finish.published finish.resources.authority instances flags tracked slot call
      current.linked current.origins current.unique stillActive factory retained
      (by simpa only [returned] using completed)
  have effect : Change (E := E) instances flags finish.resources.recorded tracked (.complete value)
      finish.resources.authority nextAuthority := by
    simpa only [returned, Handle.value] using (Change.publish stillActive factory issued)
  have next : Step program policy instances flags finish
      [stamp finish.resources.recorded.ledger tracked (.complete value)]
      ⟨⟨⟨following, Host.Recording.advance (E := E) finish.resources.recorded.ledger tracked (.complete value)⟩, nextAuthority⟩,
        PublicationRegistry.advance (E := E) finish.publications instances flags finish.resources.recorded tracked (.complete value)⟩ :=
    .record completed effect boundary
  exact ⟨returned, initialized, writable, metadata, nextAuthority, issued, owned, next.invariant current,
    by simpa only [returned, Handle.value] using published, next⟩

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CBody CCalls CCalls.Host.Recording
open CAtomicScan.ConcurrentInvariant StaticFactory
variable [interface : CInterface] {E : Type}

/-- Successful claimed initialization under the same coupled history. The
starting private reservation and private-value frame are explicit; retention
at completion and the new handle/publication are derived. -/
def InitializationContract (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (instances flags capacity : Nat) : Prop :=
  ∀ (ticks : List (Tick E)) (value : Value) (following : Concurrent.State),
    ∀ (kind : Kind) (env : Locals) (types : CLoops.Types)
    (slot : Fin capacity) (tracked : Nat)
    (environment logger : Option Address) (logging : Bool)
    (before finish : Configuration capacity) (call : Invocation) (saved : Typed.State)
    (_invariant : Invariant instances before)
    (_scope : StaticFactory.Scope env ⟨instances, [], 0⟩ ⟨flags, [], 0⟩ capacity environment logger logging)
    (_storage : InstanceSlot.Storage before.resources.recorded.runtime.heap (AtomicSlots.address instances slot))
    (_bounded : slot.val < 2^64)
    (_size : interface.types "size_t" = some .size)
    (_pointer : interface.types "Instance *" = some .pointer)
    (_double : interface.types "double" = some .float64)
    (_handleType : interface.types "fmi3Instance" = some .pointer)
    (_active : before.resources.recorded.ledger.active tracked = some call)
    (_factory : ReservationOrigin.factory call.name)
    (_found : before.resources.recorded.runtime.threads tracked = some saved)
    (_control : ClaimedReady ⟨flags, [], 0⟩ capacity slot.val (ClaimInitialization.caller model kind env types) saved)
    (_privateEntry : before.publications slot = some ⟨call.serial, false⟩)
    (_path : Transition.Events.Reaches
      (fun a ticks b => Step program policy instances flags a ticks b ∧
        InterferenceFrame {q | (AtomicSlots.address instances slot).InRecord q} tracked call.serial
          a.resources.recorded ticks b.resources.recorded)
      before ticks finish)
    (_stillActive : finish.resources.recorded.ledger.active tracked = some call)
    (_completed : Host.Step program policy finish.resources.recorded.runtime tracked (.complete value) following),
    let publications := PublicationRegistry.advance (E := E) finish.publications instances flags finish.resources.recorded tracked (.complete value)
    let ledger := Host.Recording.advance (E := E) finish.resources.recorded.ledger tracked (.complete value)
    value = Handle.value instances ⟨slot, call.serial⟩ ∧
    InstanceInitialization.Initialized following.heap (AtomicSlots.address instances slot) kind environment logger logging ∧
    InstanceSlot.Storage following.heap (AtomicSlots.address instances slot) ∧
    load following.heap ((AtomicSlots.address instances slot).member "slot") = some (.integer slot.val) ∧
    ∃ nextAuthority,
      InstanceAuthority.publish finish.resources.authority ⟨slot, call.serial⟩ = some nextAuthority ∧
      Owns nextAuthority ⟨slot, call.serial⟩ ∧
      Invariant instances ⟨⟨⟨following, ledger⟩, nextAuthority⟩, publications⟩ ∧
      PublicationRegistry.Published publications slot call.serial ∧
      Step program policy instances flags finish
        [stamp finish.resources.recorded.ledger tracked (.complete value)]
        ⟨⟨⟨following, ledger⟩, nextAuthority⟩, publications⟩

end Rumoca.FMI3.InstanceAuthority.Resources.Publication
