import RumocaFMI3.OriginBoundaries
import RumocaFMI3.AuthorizedReleaseHistories

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type} {capacity : Nat}

/-- The source-compatible captured-release theorem additionally preserves all
resource/API origins and derives absence of any ticket for the old call from
the same actual clear. The old call's return suffix may outlive slot reuse. -/
theorem captured_release_origins (program : Events.Program E) (policy : Host.Policy)
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
    (origins : CallOrigins authority before.recorded.ledger instances)
    (unique : Host.Recording.Unique before.recorded.ledger)
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
      CallOrigins newAuthority (Host.Recording.advance (E := E) before.recorded.ledger thread action) instances ∧
      NoTicket newAuthority call.serial ∧
      (∃ saved, after.threads thread = some saved ∧
        VoidReturn.Ready (StaticRelease.locals (some (AtomicSlots.address instances handle.slot)))
          StaticRelease.types saved) ∧
      (∀ other, other ≠ thread → after.threads other = before.recorded.runtime.threads other) := by
  obtain ⟨releasedCall, after, activeOrigin, name, args, actual, cleared, owners, memory,
    recorded, related, vacant, tail, others⟩ :=
    captured_authorized_clear program policy tag bindings initial before authority instances flags thread handle call flagsBound
      fresh active original entered metadata path stillActive linked borrowed calling represented
  exact ⟨releasedCall, after, activeOrigin, name, args, actual, cleared, owners, memory,
    recorded, related, vacant, clear_call_origins origins cleared,
    cleared_no_ticket origins.arguments unique cleared, tail, others⟩

end Rumoca.FMI3.InstanceAuthority
