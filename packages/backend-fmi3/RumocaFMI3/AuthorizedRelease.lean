import RumocaFMI3.InstanceAuthority
import RumocaFMI3.ReleaseClaims
import RumocaFMI3.ReleaseTail

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type} {capacity : Nat}

/-- Current caller authority enables the generated release's unique real
atomic clear. The same step consumes the resource and physical reservation,
updates computed publication, and enters a suffix independent of all instance
memory. The pending operands/control and the resource are preconditions;
reaching them from arbitrary raw importer histories is not asserted. -/
theorem authorized_clear (program : Events.Program E) (policy : Host.Policy)
    (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (handle : Handle capacity)
    (linked : Linked authority before.publications)
    (releasing : Releasing authority before.recorded.ledger thread handle instances)
    (calling : before.recorded.runtime.threads thread = some (.calling "atomic_store"
      [.pointer (some (AtomicSlots.address flags handle.slot)), CAtomicBoolean.value false] savedHeap
      (.caller .discard [.ret none] (StaticRelease.locals (some (AtomicSlots.address instances handle.slot)))
        StaticRelease.types "void" .done)))
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
  dsimp only
  obtain ⟨call, active, free, args, borrowed⟩ := releasing
  have owned := releasing_reservation linked borrowed
  obtain ⟨after, unique, released, memory, _, returned, others⟩ :=
    ConcurrentSlots.release_for_slot program tag boolean pointer bound calling represented owned
  have erased := PublicationRegistry.advance_clear before.publications instances flags before.recorded
    thread handle.slot [tag (.write (AtomicSlots.address flags handle.slot) false)] calling
  have synchronized : PublicationRegistry.advance before.publications instances flags before.recorded thread
      (.execute [tag (.write (AtomicSlots.address flags handle.slot) false)]) =
      PublicationRegistry.synchronize before.publications
        (SlotOwners.update (PublicationRegistry.reservations before.publications) handle.slot none) :=
    erased.trans (PublicationRegistry.synchronize_clear before.publications handle.slot).symm
  have projected := congrArg PublicationRegistry.reservations synchronized
  rw [PublicationRegistry.reservations_synchronize] at projected
  have consumed : clear authority handle call.serial = some (Function.update authority handle.slot none) :=
    clear_iff.mpr ⟨borrowed, rfl⟩
  refine ⟨call, after, active, free, args, unique, consumed, ?_, ?_, ?_, ?_, by simp, ?_, others⟩
  · simpa only [projected] using released
  · simpa only [projected] using memory
  · exact .record (.execute ((unique _ _).mpr ⟨rfl, rfl⟩))
  · rw [synchronized]
    exact clear_linked linked consumed
  · exact ⟨_, returned, (VoidReturn.Ready.resumed _).withHeap _⟩

end Rumoca.FMI3.InstanceAuthority
