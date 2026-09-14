import RumocaFMI3.CSRunState
import RumocaFMI3.RestartStorage
import RumocaC.StorageWrites

noncomputable section
namespace Rumoca.FMI3.StepEntry
open CMemory

theorem output_storage (stored : StepArguments.Storage heap p buffers) (time : Binary64.Value) :
    CStorage.Preserves heap (outputHeap heap buffers time) := by
  have first := CStorage.store_preserves (HistoryBodies.zero_store stored.event)
  have second := CStorage.store_preserves
    (HistoryBodies.zero_store (HistoryBodies.zero_writable stored.terminate buffers.event))
  have third := CStorage.store_preserves
    (HistoryBodies.zero_store (HistoryBodies.zero_writable
      (HistoryBodies.zero_writable stored.early buffers.event) buffers.terminate))
  have beforeLast := first.trans (second.trans third)
  obtain ⟨old, cell⟩ := stored.last
  obtain ⟨value, cell⟩ := beforeLast.cell cell
  exact beforeLast.trans (CStorage.replace_typed cell ⟨.float64, true, some (.finite time)⟩ rfl rfl)

end Rumoca.FMI3.StepEntry

namespace Rumoca.FMI3.StepAdvance
open CMemory

theorem written_storage
    (state : Reset.Writable heap (StateProofs.stateAddress p) .float64)
    (clock : Reset.Writable heap (p.member "time") .float64)
    (output : Reset.Writable heap address .float64) (value time : Binary64.Value) :
    CStorage.Preserves heap (written heap p address value time) := by
  obtain ⟨oldState, stateCell⟩ := state
  have first := CStorage.replace_typed stateCell ⟨.float64, true, some (.finite value)⟩ rfl rfl
  obtain ⟨oldTime, clockCell⟩ := clock
  obtain ⟨nextTime, clockCell⟩ := first.cell clockCell
  have second := CStorage.replace_typed clockCell ⟨.float64, true, some (.finite time)⟩ rfl rfl
  obtain ⟨oldOutput, outputCell⟩ := output
  obtain ⟨nextOutput, outputCell⟩ := (first.trans second).cell outputCell
  exact first.trans (second.trans (CStorage.replace_typed outputCell ⟨.float64, true, some (.finite time)⟩ rfl rfl))

end Rumoca.FMI3.StepAdvance

namespace Rumoca.FMI3.CSRun
open CMemory

theorem advance_storage (stored : Stored model heap p buffers reference) (after : CSHistory.ReferenceState) :
    CStorage.Preserves heap (CSHistory.written model reference.seed heap p buffers reference.current after) := by
  have outputs := StepEntry.output_storage stored.buffers reference.current.time
  have transport (address : Address) (cell : Reset.Writable heap address .float64) :
      Reset.Writable (StepEntry.outputHeap heap buffers reference.current.time) address .float64 := by
    obtain ⟨old, found⟩ := cell
    exact outputs.cell found
  exact outputs.trans (StepAdvance.written_storage (transport _ ⟨_, stored.state⟩)
    (transport _ ⟨_, stored.clock⟩) (transport _ stored.buffers.last) _ _)

end Rumoca.FMI3.CSRun

namespace Rumoca.FMI3.StepRejections
open CMemory

/-- Every classified error/discard preserves caller object descriptions
before logging, including the guards which do not write outputs. -/
theorem after_storage (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (reads : Reads reason query heap p) (selected : StepCases.Condition query reason.outcome)
    (storage : Reset.Storage heap p) : CStorage.Preserves heap (afterHeap reason query heap p) := by
  have before : CStorage.Preserves heap (beforeHeap reason query heap) := by
    by_cases writes : reason.writesOutputs = true
    · obtain ⟨buffers, outputs⟩ := buffers_present reason query selected writes
      simpa only [beforeHeap, writes, ↓reduceIte, outputHeap_of_buffers query heap buffers outputs] using
        StepEntry.output_storage (reads.outputs writes buffers outputs) query.time
    · simpa only [beforeHeap, writes, Bool.false_eq_true, ↓reduceIte] using CStorage.Preserves.refl heap
  unfold afterHeap
  split
  · exact before
  · obtain ⟨old, cell⟩ := storage.mode
    obtain ⟨value, cell⟩ := before.cell cell
    exact before.trans (CStorage.replace_typed cell ⟨.int32, true, some (.integer Mode.terminated.code)⟩ rfl rfl)

end Rumoca.FMI3.StepRejections
end
