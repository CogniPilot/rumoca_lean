import RumocaFMI3.AuthorizedRelease
import RumocaFMI3.ReleaseCapture

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type} {capacity : Nat}

/-- Compose original public entry, an actual interleaved history and current
caller permission. The pending clear operands and continuation are derived
from generated code. Interference must protect metadata only while current
control still needs to read it; no such frame remains after operand capture. -/
theorem captured_authorized_clear (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E) (bindings : StaticRelease.Bindings program tag)
    (initial : Host.Recording.State) (before : PublicationRegistry.Configuration capacity)
    (authority : State capacity) (instances flags thread : Nat) (handle : Handle capacity)
    (call : Host.Recording.Invocation)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨flags, [], 0⟩)))
    (fresh : Host.Recording.Fresh initial.ledger)
    (active : initial.ledger.active thread = some call)
    (original : call.name = StaticRelease.function.signature.name ∧ call.args = [handle.value instances])
    (entered : initial.runtime.threads thread = some (.calling StaticRelease.function.signature.name
      [handle.value instances] entryHeap .done))
    (metadata : StaticRelease.ConcurrentInvariant.Metadata (some (AtomicSlots.address instances handle.slot))
      handle.slot.val initial.runtime.heap)
    (path : Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        Host.Recording.FootprintFrame (StaticRelease.Capture.footprint
          (some (AtomicSlots.address instances handle.slot))) thread call.serial a ticks b)
      initial ticks before.recorded)
    (stillActive : before.recorded.ledger.active thread = some call)
    (linked : Linked authority before.publications)
    (borrowed : authority handle.slot = some ⟨handle.lease, .releasing call.serial⟩)
    (calling : before.recorded.runtime.threads thread = some (.calling "atomic_store" args savedHeap stack))
    (represented : SlotOwners.Represents flags before.recorded.runtime.heap
      (PublicationRegistry.reservations before.publications)) :
    let effects := [tag (.write (AtomicSlots.address flags handle.slot) false)]
    let action := Host.Action.execute effects
    let newAuthority := Function.update authority handle.slot none
    let publications := PublicationRegistry.advance before.publications instances flags before.recorded thread action
    ∃ (call : Host.Recording.Invocation) (after : Concurrent.State),
      (Host.Recording.stamp before.recorded.ledger thread action).origin = some call ∧
      call.name = StaticRelease.function.signature.name ∧ call.args = [handle.value instances] ∧
      (∀ events target, Concurrent.Step program before.recorded.runtime thread events target ↔
        events = effects ∧ target = after) ∧
      clear authority handle call.serial = some newAuthority ∧
      SlotOwners.release (PublicationRegistry.reservations before.publications) handle.slot handle.lease =
        some (PublicationRegistry.reservations publications) ∧
      SlotOwners.Represents flags after.heap (PublicationRegistry.reservations publications) ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread action]
        ⟨⟨after, Host.Recording.advance (E := E) before.recorded.ledger thread action⟩, publications⟩ ∧
      Linked newAuthority publications ∧ newAuthority handle.slot = none ∧
      (∃ saved, after.threads thread = some saved ∧
        VoidReturn.Ready (StaticRelease.locals (some (AtomicSlots.address instances handle.slot)))
          StaticRelease.types saved) ∧
      (∀ other, other ≠ thread → after.threads other = before.recorded.runtime.threads other) := by
  have initialReady : Host.Recording.CurrentSelected
      (StaticRelease.Capture.Protected (some (AtomicSlots.address instances handle.slot))
        ⟨flags, [], 0⟩ handle.slot.val) thread call.serial initial := by
    intro originalCall saved chosen _ found
    cases Option.some.inj (chosen.symm.trans active)
    cases Option.some.inj (found.symm.trans entered)
    exact .inl ⟨.entry _, fun _ => metadata⟩
  have current := (StaticRelease.Capture.history_protected program policy tag bindings flagsBound
    (fresh thread call active) initialReady path).2.1
  have ready := current call _ stillActive rfl calling
  obtain ⟨_, arguments, continuation⟩ := StaticRelease.Capture.atomic_control ready rfl
  have argumentsEq : args = [.pointer (some (AtomicSlots.address flags handle.slot)), CAtomicBoolean.value false] := by
    simpa [Address.index, AtomicSlots.address] using arguments
  rw [argumentsEq, continuation] at calling
  exact authorized_clear program policy tag bindings.boolean bindings.atomicPointer bindings.atomicBound before authority
    instances flags thread handle linked ⟨call, stillActive, original.1, original.2, borrowed⟩ calling represented



/-- Public-history contract for the actual captured release. Complete legal
resource retention and the control-dependent metadata frame remain explicit;
the concrete source theorem supplies the generated program and all bindings. -/
def ReleaseContract (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E) (instances flags capacity : Nat) : Prop :=
  ∀ (initial : Host.Recording.State) (before : PublicationRegistry.Configuration capacity)
    (authority : State capacity) (thread : Nat) (handle : Handle capacity)
    (call : Host.Recording.Invocation) (entryHeap savedHeap : Heap)
    (args : List Value) (stack : Typed.Continuation) (ticks : List (Host.Recording.Tick E)),
    Host.Recording.Fresh initial.ledger →
    initial.ledger.active thread = some call →
    (call.name = StaticRelease.function.signature.name ∧ call.args = [handle.value instances]) →
    initial.runtime.threads thread = some (.calling StaticRelease.function.signature.name
      [handle.value instances] entryHeap .done) →
    StaticRelease.ConcurrentInvariant.Metadata (some (AtomicSlots.address instances handle.slot))
      handle.slot.val initial.runtime.heap →
    Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        Host.Recording.FootprintFrame (StaticRelease.Capture.footprint
          (some (AtomicSlots.address instances handle.slot))) thread call.serial a ticks b)
      initial ticks before.recorded →
    before.recorded.ledger.active thread = some call →
    Linked authority before.publications →
    authority handle.slot = some ⟨handle.lease, .releasing call.serial⟩ →
    before.recorded.runtime.threads thread = some (.calling "atomic_store" args savedHeap stack) →
    SlotOwners.Represents flags before.recorded.runtime.heap
      (PublicationRegistry.reservations before.publications) →
    let effects := [tag (.write (AtomicSlots.address flags handle.slot) false)]
    let action := Host.Action.execute effects
    let newAuthority := Function.update authority handle.slot none
    let publications := PublicationRegistry.advance before.publications instances flags before.recorded thread action
    ∃ (call : Host.Recording.Invocation) (after : Concurrent.State),
      (Host.Recording.stamp before.recorded.ledger thread action).origin = some call ∧
      call.name = StaticRelease.function.signature.name ∧ call.args = [handle.value instances] ∧
      (∀ events target, Concurrent.Step program before.recorded.runtime thread events target ↔
        events = effects ∧ target = after) ∧
      clear authority handle call.serial = some newAuthority ∧
      SlotOwners.release (PublicationRegistry.reservations before.publications) handle.slot handle.lease =
        some (PublicationRegistry.reservations publications) ∧
      SlotOwners.Represents flags after.heap (PublicationRegistry.reservations publications) ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread action]
        ⟨⟨after, Host.Recording.advance (E := E) before.recorded.ledger thread action⟩, publications⟩ ∧
      Linked newAuthority publications ∧ newAuthority handle.slot = none ∧
      (∃ saved, after.threads thread = some saved ∧
        VoidReturn.Ready (StaticRelease.locals (some (AtomicSlots.address instances handle.slot)))
          StaticRelease.types saved) ∧
      (∀ other, other ≠ thread → after.threads other = before.recorded.runtime.threads other)

end Rumoca.FMI3.InstanceAuthority
