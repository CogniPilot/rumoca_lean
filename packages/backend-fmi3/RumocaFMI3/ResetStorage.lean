import RumocaC.StoreRunInvariant
import RumocaC.AtomicFrame
import RumocaC.Subobjects
import RumocaFMI3.ResetCalls
import RumocaC.StorageTransfer

namespace Rumoca.FMI3
open CMemory

theorem Reset.Storage.preserved (stored : Reset.Storage heap p) (preserved : CStorage.Preserves heap after) :
    Reset.Storage after p := by
  have keep {address type} (cell : Reset.Writable heap address type) : Reset.Writable after address type := by
    obtain ⟨old, found⟩ := cell
    exact preserved.cell found
  exact ⟨keep stored.state, keep stored.time, keep stored.minimum, keep stored.event,
    keep stored.completed, keep stored.stop, keep stored.stopDefined, keep stored.mode⟩

theorem Reset.Storage.record_preserved (storage : Reset.Storage before p)
    (frame : ∀ query, p.InRecord query → after query = before query) : Reset.Storage after p := by
  have field (name : String) (type : CType) (stored : Reset.Writable before (p.member name) type) :
      Reset.Writable after (p.member name) type := by
    obtain ⟨value, found⟩ := stored
    exact ⟨value, (frame _ (p.member_in_record name)).trans found⟩
  refine ⟨?_, field "time" _ storage.time, field "timeMin" _ storage.minimum,
    field "eventTime" _ storage.event, field "lastCompleted" _ storage.completed,
    field "stop" _ storage.stop, field "stopDefined" _ storage.stopDefined, field "mode" _ storage.mode⟩
  obtain ⟨value, found⟩ := storage.state
  exact ⟨value, (frame _ ((p.member_in_record "model").member "x")).trans found⟩

end Rumoca.FMI3


noncomputable section
namespace Rumoca.FMI3.Reset
open CMemory

/-- Actual reset retains the original typed storage and reservations. This
fact is shared by both interfaces and by reset with interleaved accesses. -/
theorem preserves (model : Solve.FMI3Model source) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (stored : Storage heap p)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code)) :
    CStorage.Preserves heap (finalHeap heap p) ∧ CAtomicBoolean.Preserves heap (finalHeap heap p) := by
  let literals : CLiteralAddresses := fun _ => none
  letI : CInterface := cInterface literals
  have run := body_run (static := ⟨literals⟩) model signature rfl heap p kind mode stored kindValue modeValue
  exact ⟨CStoreInvariant.body_run ⟨CStorage.Preserves.refl, fun _ _ _ _ => CStorage.store_preserves⟩
    (fun a b => a.trans b) run,
    CStoreInvariant.body_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b) run⟩

end Rumoca.FMI3.Reset
end
