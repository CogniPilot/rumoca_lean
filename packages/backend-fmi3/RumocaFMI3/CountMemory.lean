import RumocaFMI3.CountEnvironment
import RumocaFMI3.Float64RejectionMemory
import RumocaC.StorageRegion

/-! Storage consequences of the actual count write. These are the handoff
premises needed to insert count observations into initialization and ME
histories, without assuming a later instance or caller heap is valid. -/
noncomputable section
namespace Rumoca.FMI3.CountQueries
open CMemory StaticFactory

theorem written_store (events : Bool) (heap : Heap) (buffer : Address) (old : Option Value)
    (storage : heap buffer = some ⟨.size, true, old⟩) :
    store heap buffer (.integer (count events)) = some (written events heap buffer) := by
  cases events <;> simp [store, storage, convert, written, count]

/-- A successful count write preserves the model, reset storage, reservation
map and every other cell. The output is original writable caller storage
outside the instance record, not an assumed valid post-call heap. -/
theorem written_memory (events : Bool) (heap : Heap) (p buffer : Address)
    (kind : Kind) (mode : Mode) (state : ModelExchange.State) (time : Binary64.Value)
    (objects : Objects) (owners : SlotOwners.State objects.capacity) (old : Option Value)
    (storage : heap buffer = some ⟨.size, true, old⟩)
    (instanceStored : Float64Access.Instance heap p kind mode state time)
    (reset : Reset.Storage heap p)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (outside : ¬ p.InRecord buffer) :
    Float64Access.Instance (written events heap buffer) p kind mode state time ∧
    Reset.Storage (written events heap buffer) p ∧
    SlotOwners.Represents objects.flagsBlock (written events heap buffer) owners ∧
    CStorage.Preserves heap (written events heap buffer) ∧
    CReadOnly.Preserves heap (written events heap buffer) ∧
    CAtomicBoolean.Preserves heap (written events heap buffer) ∧
    (∀ q, q ≠ buffer → written events heap buffer q = heap q) := by
  have executed := written_store events heap buffer old storage
  have kept := CStorage.store_preserves executed
  have atomic := CAtomicBoolean.ordinary_store_preserves executed
  have record : ∀ q, p.InRecord q → written events heap buffer q = heap q := by
    intro q inside
    apply frame
    intro same
    exact outside (same ▸ inside)
  exact ⟨instanceStored.record_preserved record, reset.preserved kept,
    SlotOwners.ordinary_preserves ownership atomic, kept, CReadOnly.store_preserves executed,
    atomic, frame events heap buffer⟩

/-- The error helper changes the mode before logging. Every represented
callback return preserves the host's protected region; no return is assumed. -/
theorem failed_memory (objects : Objects) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (heap : Heap) (p : Address)
    (stored : Float64Access.Instance heap p kind mode state time)
    (reset : Reset.Storage heap p)
    (inPool : p.block = objects.instances.block)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (callbackFrame : Float64Rejection.Frame objects retained (LifecycleBodies.writeMode heap p .terminated) after)
    (callbackReadonly : CReadOnly.Preserves (LifecycleBodies.writeMode heap p .terminated) after) :
    Float64Access.Instance after p kind .terminated state time ∧
    Reset.Storage after p ∧ SlotOwners.Represents objects.flagsBlock after owners ∧
    CStorage.PreservesOn (Float64Rejection.Protected objects retained) heap after ∧
    CReadOnly.Preserves heap after ∧
    (∀ q, Float64Rejection.Protected objects retained q → q ≠ p.member "mode" → after q = heap q) := by
  have modeFrame := LifecycleBodies.write_storage heap p _ .terminated stored.mode
  exact ⟨stored.failed.record_preserved (callbackFrame.record inPool),
    (reset.preserved modeFrame.1).record_preserved (callbackFrame.record inPool),
    callbackFrame.owners (SlotOwners.ordinary_preserves ownership modeFrame.2.2),
    (modeFrame.1.on _).trans (.of_frame callbackFrame),
    modeFrame.2.1.trans callbackReadonly,
    fun q guarded different => (callbackFrame q guarded).trans
      (LifecycleBodies.write_frame heap p q .terminated different)⟩

end Rumoca.FMI3.CountQueries
end
