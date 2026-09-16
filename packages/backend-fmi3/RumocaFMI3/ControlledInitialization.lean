import RumocaFMI3.PoolControls
import RumocaFMI3.RetainedInitialization

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable [CInterface] {E : Type} {program : Events.Program E} {policy : Host.Policy}
  {capacity : Nat} {before after : Configuration capacity}

theorem controls_erases
    (path : Transition.Events.Reaches
      (fun a ticks b => Step program policy instances flags a ticks b ∧ Controls program instances a)
      before ticks after) :
    Transition.Events.Reaches (Step program policy instances flags) before ticks after := by
  induction path with
  | refl => exact .refl _
  | next first rest ih => exact .next first.1 ih

/-- Construct the complete private interference frame from current C controls
on the same coupled path. Intermediate activity and reservation retention are
derived from the final original invocation and the computed ledger. -/
theorem controlled_history
    (path : Transition.Events.Reaches
      (fun a ticks b => Step program policy instances flags a ticks b ∧ Controls program instances a)
      before ticks after)
    (invariant : Invariant instances before)
    (privateEntry : before.publications slot = some ⟨call.serial, false⟩)
    (active : before.resources.recorded.ledger.active tracked = some call)
    (stillActive : after.resources.recorded.ledger.active tracked = some call)
    (memory : MemoryPolicy policy instances) :
    Transition.Events.Reaches
      (fun a ticks b => Step program policy instances flags a ticks b ∧
        Host.Recording.InterferenceFrame {q | (AtomicSlots.address instances slot).InRecord q}
          tracked call.serial a.resources.recorded ticks b.resources.recorded)
      before ticks after := by
  induction path with
  | refl => exact .refl _
  | next first rest ih =>
    have nextInvariant := first.1.invariant invariant
    have suffix := Resources.history_erases (history_invariant (controls_erases rest) nextInvariant).2.1
    have advance := (Host.Recording.history_issued
      (Transition.Events.Reaches.next first.1.resources.erases (.refl _))).1
    have nextActive := Host.Recording.history_retained suffix
      (Nat.lt_of_lt_of_le (invariant.fresh tracked call active) advance) stillActive
    have frame := Host.Recording.controls_frame
      (controls_private invariant active privateEntry first.2 memory) first.1.resources.erases
    exact .next ⟨first.1, frame⟩
      (ih nextInvariant (first.1.private_reservation invariant privateEntry active nextActive)
        nextActive stillActive)

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CBody CCalls CCalls.Host.Recording
open CAtomicScan.ConcurrentInvariant StaticFactory
variable [interface : CInterface] {E : Type}

/-- Initialization from destination-checked actual controls and explicit
foreign/importer effects. The interference frame is derived from that same
coupled prefix; all earlier return, storage and publication guarantees remain. -/
def ControlledInitializationContract (program : Events.Program E) (policy : Host.Policy)
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
    (_memory : MemoryPolicy policy instances)
    (_path : Transition.Events.Reaches
      (fun a ticks b => Step program policy instances flags a ticks b ∧
        Controls program instances a)
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


/-- Derive initialization and handle issuance without a supplied per-step
internal memory frame. Establishing Controls from complete public entry and
pending-call invariants remains a separate protocol obligation. -/
theorem initialized_from_controls (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (instances flags capacity : Nat) :
    ControlledInitializationContract program policy model instances flags capacity := by
  intro ticks value following kind env types slot tracked environment logger logging before finish call saved
    invariant scope storage bounded size pointer double handleType active factory found control privateEntry
    memory path stillActive completed
  exact initialized_from_history program policy model kind env types instances flags slot tracked
    environment logger logging before finish call saved invariant scope storage bounded size pointer double
    handleType active factory found control privateEntry
    (controlled_history path invariant privateEntry active stillActive memory) stillActive completed

end Rumoca.FMI3.InstanceAuthority.Resources.Publication
