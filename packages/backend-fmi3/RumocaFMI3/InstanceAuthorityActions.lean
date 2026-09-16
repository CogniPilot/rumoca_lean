import RumocaFMI3.InstanceAuthority
import RumocaFMI3.ReleaseInvariant

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat}

variable [interface : CInterface] {E : Type}

/-- Actual public entry consumes the client's resource using the ledger's
fresh invocation number. The public name and erased handle are fixed by the
same C invocation, rather than by an arbitrary per-step release annotation. -/
theorem release_enter (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (handle : Handle capacity)
    (linked : Linked authority before.publications) (owned : Owns authority handle)
    (actual : Host.Step program policy before.recorded.runtime thread
      (.invoke StaticRelease.function.signature.name [handle.value instances]) after) :
    let action := Host.Action.invoke (E := E) StaticRelease.function.signature.name [handle.value instances]
    let ledger := Host.Recording.advance before.recorded.ledger thread action
    ∃ following,
      enter authority handle before.recorded.ledger.next .release = some following ∧
      Releasing following ledger thread handle instances ∧
      Linked following before.publications ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread action]
        ⟨⟨after, ledger⟩, before.publications⟩ ∧
      (∃ saved, after.threads thread = some saved ∧
        StaticRelease.ConcurrentInvariant.Ready (some (AtomicSlots.address instances handle.slot))
          ⟨flags, [], 0⟩ handle.slot.val .done saved) := by
  dsimp only
  let following := Function.update authority handle.slot (some ⟨handle.lease, .releasing before.recorded.ledger.next⟩)
  have entered : enter authority handle before.recorded.ledger.next .release = some following :=
    enter_iff.mpr ⟨owned, rfl⟩
  refine ⟨following, entered, ?_, enter_linked linked entered, .record actual, ?_⟩
  · refine ⟨⟨before.recorded.ledger.next, StaticRelease.function.signature.name, [handle.value instances]⟩, ?_, rfl, rfl, ?_⟩
    · simp [Host.Recording.advance, Host.Recording.bind]
    · simp [following]
  · rw [(Host.invoke_iff.mp actual).2.2]
    refine ⟨.calling StaticRelease.function.signature.name [handle.value instances] (fun _ => none) .done, ?_, ?_⟩
    · simp [Concurrent.update, Concurrent.control, Concurrent.withHeap]
    · exact .entry _

/-- A real successful factory completion issues a handle for its recorded
serial. Resource vacancy follows from the reservation still being private.
This rule cannot mint authority by matching an arbitrary existing pointer. -/
theorem factory_complete (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (slot : Fin capacity) (call : Host.Recording.Invocation)
    (linked : Linked authority before.publications)
    (active : before.recorded.ledger.active thread = some call)
    (factory : ReservationOrigin.factory call.name)
    (privateEntry : before.publications slot = some ⟨call.serial, false⟩)
    (actual : Host.Step program policy before.recorded.runtime thread
      (.complete (.pointer (some (AtomicSlots.address instances slot)))) after) :
    let handle : Handle capacity := ⟨slot, call.serial⟩
    let action := Host.Action.complete (E := E) (handle.value instances)
    let published := PublicationRegistry.advance before.publications instances flags before.recorded thread action
    ∃ following,
      publish authority handle = some following ∧ Owns following handle ∧ Linked following published ∧
      PublicationRegistry.Published published slot call.serial ∧
      PublicationRegistry.Observed instances slot call.serial
        (Host.Recording.stamp before.recorded.ledger thread action) ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread action]
        ⟨⟨after, Host.Recording.advance (E := E) before.recorded.ledger thread action⟩, published⟩ := by
  dsimp only
  have vacant := private_vacant linked privateEntry
  have issued : publish authority ⟨slot, call.serial⟩ =
      some (Function.update authority slot (some ⟨call.serial, .client⟩)) :=
    publish_iff.mpr ⟨vacant, rfl⟩
  refine ⟨_, issued, published_owns issued, ?_, ?_, ?_, .record actual⟩
  · simpa [PublicationRegistry.advance, PublicationRegistry.observe, Handle.value, active,
      factory, ReservationRegistry.slotAt_address] using publish_linked linked privateEntry issued
  · exact PublicationRegistry.observe_owned active factory privateEntry
  · exact ⟨call, active, rfl, factory, rfl⟩

end Rumoca.FMI3.InstanceAuthority
