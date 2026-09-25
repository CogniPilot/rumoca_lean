import RumocaFMI3.TensorReset
import RumocaFMI3.TensorMetadata
import RumocaC.Decimal
import RumocaC.RealConstants

/-! The restored regions carry the declared start values.

The model description declares one flattened `start` entry per element of every
state-shaped array variable (`TensorMetadata.startEntries`). The restore block the
factory and `fmi3Reset` share leaves every state-shaped region of the record
reading values whose binary64 meaning is exactly the natural number each entry
spells, so a newly instantiated or reset instance holds the declared start values
of its state and its inputs. -/
namespace Rumoca.FMI3.TensorStartValues
open CMemory CMemory.TensorView

/-- Every state-shaped region of the restored record reads the values its declared
start entries denote. -/
theorem restored_start (shape : Tensor.Shape) (hasInput hasOutput : Bool) (heap : Heap) (p : Address)
    (name : String) (declared : (name, shape) ∈ TensorStorage.regions shape hasInput hasOutput) :
    ∃ v : Values shape,
      Reads (TensorReset.restoreHeap heap p (TensorStorage.regions shape hasInput hasOutput)) (p.member name) v ∧
      ∀ (k : Fin shape.volume) (n : Nat),
        CDecimal.Denotes ((TensorMetadata.startEntries shape)[k.val]'(by
          rw [TensorMetadata.startEntries_length]; exact k.isLt)).toList n →
        Binary64.value v[k] = n := by
  refine ⟨TensorReset.zeroValues shape,
    TensorReset.restoreHeap_reads heap p _ (TensorStorage.regions_distinct shape hasInput hasOutput)
      (name, shape) declared, fun k n denotes => ?_⟩
  have spelled : (TensorMetadata.startEntries shape)[k.val]'(by
      rw [TensorMetadata.startEntries_length]; exact k.isLt) = "0" := by
    simp [TensorMetadata.startEntries]
  rw [spelled] at denotes
  obtain ⟨_, _, valued⟩ := denotes
  have zero : n = 0 := by simpa [CDecimal.value] using valued.symm
  subst zero
  simp [TensorReset.zeroValues, CBody.value_positiveZero]

end Rumoca.FMI3.TensorStartValues
