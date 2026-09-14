import RumocaFMI3.CountMemory
import RumocaFMI3.MEFailureMemory

/-! Count-output storage for the existing mixed ME histories.
The caller supplies a separate size_t cell; no numerical buffer is retyped. -/
noncomputable section
namespace Rumoca.FMI3.MECountCalls
open CMemory StaticFactory

theorem written_frame (events : Bool) (heap : Heap) (output : Address)
    (objects : Objects) (addresses : String → Address) (buffer : Address)
    (outside : ¬ MEFailure.Protected objects addresses buffer output) :
    MEFailure.ProtectedFrame objects addresses buffer heap (CountQueries.written events heap output) := by
  intro q guarded
  exact CountQueries.frame events heap output q (fun same => outside (same ▸ guarded))

/-- Derive every ME simulation handoff after a successful count write.
Only the original caller count cell may change; the old ME buffer contract
does not acquire unrelated size_t-cell requirements for its other actions. -/
theorem written_memory (events : Bool) (heap : Heap) (p output : Address)
    (objects : Objects) (addresses : String → Address) (buffer : Address)
    (clock : Time.Clock) (reference : MENumericalHistory.ReferenceState)
    (owners : SlotOwners.State objects.capacity) (old : Option Value)
    (storage : heap output = some ⟨.size, true, old⟩)
    (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (reset : Reset.Storage heap p)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (inPool : p.block = objects.instances.block)
    (outside : ¬ MEFailure.Protected objects addresses buffer output) :
    MENumericalHistory.Stored (CountQueries.written events heap output) p clock reference addresses buffer ∧
    Reset.Storage (CountQueries.written events heap output) p ∧
    SlotOwners.Represents objects.flagsBlock (CountQueries.written events heap output) owners ∧
    CStorage.Preserves heap (CountQueries.written events heap output) ∧
    CReadOnly.Preserves heap (CountQueries.written events heap output) ∧
    MEFailure.ProtectedFrame objects addresses buffer heap (CountQueries.written events heap output) := by
  have executed := CountQueries.written_store events heap output old storage
  have frame := written_frame events heap output objects addresses buffer outside
  have numerical := frame.numerical inPool
  exact ⟨stored.framed numerical, numerical.reset_storage reset, frame.owners ownership,
    CStorage.store_preserves executed, CReadOnly.store_preserves executed, frame⟩

end Rumoca.FMI3.MECountCalls
end
