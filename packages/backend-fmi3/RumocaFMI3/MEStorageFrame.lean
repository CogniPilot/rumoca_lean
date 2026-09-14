import RumocaFMI3.MENumericalMemory
import RumocaC.StorageTransfer
import RumocaC.Subobjects

/-! ME caller buffers require writable storage, not unchanged payloads.
These frames allow compatible caller-buffer aliases while retaining every
instance field, model value and reference-control invariant. -/
noncomputable section
namespace Rumoca.FMI3.MEHistory
open CMemory

theorem Buffers.storage_preserved (buffers : Buffers before addresses)
    (preserved : CStorage.Preserves before after) : Buffers after addresses := by
  intro layout member
  obtain ⟨old, found⟩ := buffers layout member
  exact preserved.cell found

theorem Stored.record_storage_preserved (stored : Stored heap p clock reference model addresses)
    (record : ∀ q, p.InRecord q → after q = heap q)
    (storage : CStorage.Preserves heap after) : Stored after p clock reference model addresses := by
  have fields (name : String) := record (p.member name) (p.member_in_record name)
  have state := record (StateProofs.stateAddress p) ((p.member_in_record "model").member "x")
  refine ⟨?_, (fields "mode").trans stored.mode, ?_, stored.history, ?_, ?_, ?_,
    stored.buffers.storage_preserved storage, stored.outside⟩
  · simpa only [load, fields] using stored.kind
  · exact ⟨(fields "time").trans stored.clockStored.time,
      (fields "timeMin").trans stored.clockStored.minimum,
      (fields "eventTime").trans stored.clockStored.eventTime,
      (fields "lastCompleted").trans stored.clockStored.lastCompleted⟩
  · simpa only [StateProofs.Represents, load, state] using stored.modelStored
  · simpa only [load, fields] using stored.stopDefined
  · intro stop selected
    simpa only [load, fields] using stored.stopValue stop selected

end Rumoca.FMI3.MEHistory

namespace Rumoca.FMI3.MENumericalHistory
open CMemory

theorem Stored.record_storage_preserved (stored : Stored heap p clock reference addresses buffer)
    (record : ∀ q, p.InRecord q → after q = heap q)
    (storage : CStorage.Preserves heap after) : Stored after p clock reference addresses buffer := by
  obtain ⟨old, cell⟩ := stored.bufferCell
  exact ⟨stored.control.record_storage_preserved record storage,
    (record _ ((p.member_in_record "model").member "x")).trans stored.stateCell,
    storage.cell cell, stored.bufferOutside, stored.bufferSeparate⟩

end Rumoca.FMI3.MENumericalHistory
end
