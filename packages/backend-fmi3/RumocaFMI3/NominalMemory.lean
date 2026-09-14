import RumocaFMI3.NominalEnvironment
import RumocaFMI3.Float64RejectionMemory
import RumocaC.StorageRegion
import RumocaFMI3.MEStorageFrame

/-! Memory effects of the actual nominal write. Original writable storage
supplies the post-call resources; a later valid instance is not a premise. -/
noncomputable section
namespace Rumoca.FMI3.Nominals
open CMemory StaticFactory

theorem written_store (heap : Heap) (buffer : Address) (old : Option Value)
    (storage : heap buffer = some ⟨.float64, true, old⟩) :
    store heap buffer (.finite Binary64.one) = some (written heap buffer) := by
  simp [store, storage, convert, written, Value.finite]

/-- A caller output may reuse another compatible caller cell. It must be
outside this instance record to preserve the model and its configuration. -/
theorem written_memory (heap : Heap) (p buffer : Address)
    (kind : Kind) (mode : Mode) (state : ModelExchange.State) (time : Binary64.Value)
    (objects : Objects) (owners : SlotOwners.State objects.capacity) (old : Option Value)
    (storage : heap buffer = some ⟨.float64, true, old⟩)
    (instanceStored : Float64Access.Instance heap p kind mode state time)
    (reset : Reset.Storage heap p)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (outside : ¬ p.InRecord buffer) :
    Float64Access.Instance (written heap buffer) p kind mode state time ∧
    Reset.Storage (written heap buffer) p ∧
    SlotOwners.Represents objects.flagsBlock (written heap buffer) owners ∧
    CStorage.Preserves heap (written heap buffer) ∧
    CReadOnly.Preserves heap (written heap buffer) ∧
    CAtomicBoolean.Preserves heap (written heap buffer) ∧
    (∀ q, q ≠ buffer → written heap buffer q = heap q) := by
  have executed := written_store heap buffer old storage
  have kept := CStorage.store_preserves executed
  have atomic := CAtomicBoolean.ordinary_store_preserves executed
  have record : ∀ q, p.InRecord q → written heap buffer q = heap q := by
    intro q inside
    apply frame
    intro same
    exact outside (same ▸ inside)
  exact ⟨instanceStored.record_preserved record, reset.preserved kept,
    SlotOwners.ordinary_preserves ownership atomic, kept, CReadOnly.store_preserves executed,
    atomic, frame heap buffer⟩

/-- Nominal output may alias the reusable ME float buffer or a compatible
control output. The caller bank keeps its storage, without a payload-frame
assumption that would exclude these legal aliases. -/
theorem written_me_memory (heap : Heap) (p output : Address)
    (objects : Objects) (owners : SlotOwners.State objects.capacity)
    (addresses : String → Address) (buffer : Address)
    (clock : Time.Clock) (reference : MENumericalHistory.ReferenceState) (old : Option Value)
    (storage : heap output = some ⟨.float64, true, old⟩)
    (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (reset : Reset.Storage heap p)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (outside : ¬ p.InRecord output) :
    MENumericalHistory.Stored (written heap output) p clock reference addresses buffer ∧
    Reset.Storage (written heap output) p ∧
    SlotOwners.Represents objects.flagsBlock (written heap output) owners ∧
    CStorage.Preserves heap (written heap output) ∧
    CReadOnly.Preserves heap (written heap output) ∧
    CAtomicBoolean.Preserves heap (written heap output) ∧
    (∀ q, q ≠ output → written heap output q = heap q) := by
  have executed := written_store heap output old storage
  have kept := CStorage.store_preserves executed
  have atomic := CAtomicBoolean.ordinary_store_preserves executed
  have record : ∀ q, p.InRecord q → written heap output q = heap q := by
    intro q inside
    exact frame heap output q (fun same => outside (same ▸ inside))
  exact ⟨stored.record_storage_preserved record kept, reset.preserved kept,
    SlotOwners.ordinary_preserves ownership atomic, kept, CReadOnly.store_preserves executed,
    atomic, frame heap output⟩

end Rumoca.FMI3.Nominals
end
