import RumocaFMI3.MEAtomicFrames
import RumocaFMI3.TerminationRelease

noncomputable section
namespace Rumoca.FMI3.MEHistory

def ReferenceState.Live (reference : ReferenceState) : Prop :=
  reference.mode = .event ∨ reference.mode = .continuous

theorem Action.next_live (action : Action) (live : reference.Live) : (action.next reference).Live := by
  cases action with
  | setTime _ => exact live
  | updateDiscrete => exact live
  | completed _ => exact live
  | enter entry => cases entry <;> simp [Action.next, ReferenceState.Live, EventEntry.Entry.after]

theorem ReferenceTrace.live (admitted : ReferenceTrace reference actions final) (live : reference.Live) :
    final.Live := by
  induction admitted with
  | nil => exact live
  | cons _ _ ih => exact ih (Action.next_live _ live)

theorem ReferenceState.Live.terminate {reference : ReferenceState} (live : reference.Live) :
    Reference.Allowed .terminate .me reference.mode := by
  rcases live with mode | mode <;> simp [Reference.Allowed, mode]

end Rumoca.FMI3.MEHistory

namespace Rumoca.FMI3.MEHistory
open CTree CMemory StaticFactory

theorem slot_outside (outside : Buffers.Outside p addresses) : Outside p addresses (p.member "slot") := by
  refine ⟨by simp, by simp, by simp, by simp, by simp, ?_⟩
  intro name member same
  have blocks := congrArg Address.block same
  exact outside name member (by simpa using blocks.symm)

/-- An owned ME instance runs its admitted control history and then terminates
and releases. The lease at the end of the history is derived from ordinary
typed writes; it is not supplied again. Released handles gain no future-call
validity from this proposition. -/
def ReleaseContract [interface : CInterface] (objects : Objects)
    (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E) : Prop :=
  ∀ (heap : Heap) (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity)
    (owner : Nat) (clock : Time.Clock) (reference final : ReferenceState) (model : ModelExchange.State)
    (addresses : String → Address) (actions : List Action),
    let p := objects.instances.index slot.val
    Stored heap p clock reference model addresses → reference.Live →
    ReferenceTrace reference actions final →
    SlotOwners.Represents objects.flagsBlock heap owners → owners slot = some owner →
    load heap (p.member "slot") = some (.integer slot.val) →
    ∃ after finalClock,
      Calls program p addresses heap actions after ∧ Stored after p finalClock final model addresses ∧
      let terminated := LifecycleBodies.writeMode after p .terminated
      let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
      SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
      SlotOwners.Represents objects.flagsBlock released (SlotOwners.update owners slot none) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
        behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
      (∀ query, Outside p addresses query → query ≠ AtomicSlots.address objects.flagsBlock slot →
        released query = heap query)

theorem release_correct [interface : CInterface] (objects : Objects)
    (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (quiet : Quiet program) (finish : Termination.ReleaseContract objects program tag) :
    ReleaseContract objects program tag := by
  intro heap slot owners owner clock reference final model addresses actions
  let p := objects.instances.index slot.val
  dsimp only
  intro stored live admitted represented owned metadata
  obtain ⟨after, finalClock, called, storedAfter, atomic, framed⟩ := trace_atomic_frame program quiet stored admitted
  have representedAfter := SlotOwners.ordinary_preserves represented atomic
  have metadataAfter : load after (p.member "slot") = some (.integer slot.val) := by
    simpa only [p, load, framed _ (slot_outside stored.outside)] using metadata
  obtain ⟨terminated, discharged, releasedOwners, releasedFrame, freed⟩ :=
    finish after slot owners owner .me final.mode storedAfter.kind storedAfter.mode
      (admitted.live live).terminate representedAfter owned metadataAfter
  refine ⟨after, finalClock, called, storedAfter, terminated, discharged, releasedOwners, freed, ?_⟩
  intro query outside flag
  exact (releasedFrame query outside.2.1 flag).trans (framed query outside)

end Rumoca.FMI3.MEHistory
