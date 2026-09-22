import RumocaC.TensorMultiplicationTotal

/-! Mandatory actual-helper text and total finite-input multiplication behavior.
This strengthens numerical coverage without admitting new source syntax or
claiming total source trajectories, trapping behavior or native correspondence. -/
namespace Rumoca.CTensor.MultiplicationTotal
open CMemory CMemory.TensorView Rumoca.Tensor

def StorageContract : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions) {shape : Shape}
    (a b : Values shape) (heap : Heap) (left right output : Address),
  definitions (function .mul).signature.name = some (function .mul) →
  HeaderTypes interface → Reads heap left a → Reads heap right b →
  Writable heap output shape.volume →
  Separate output left shape.volume → Separate output right shape.volume →
  shape.volume < 2 ^ 64 →
    (∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling (function .mul).signature.name (argumentValues left right output shape.volume) heap .done)
        behavior ↔ behavior = .terminates (EncodedTensor.written heap output (result a b) shape.volume)) ∧
    EncodedTensor.ReadsBits (EncodedTensor.written heap output (result a b) shape.volume)
      output (result a b) ∧
    (∀ i : Fin shape.volume, Binary64.MultipliesResult a[i] b[i] (Float64.decode (result a b)[i])) ∧
    (∀ q, (∀ i < shape.volume, q ≠ output.index i) →
      EncodedTensor.written heap output (result a b) shape.volume q = heap q)

theorem storage_correct : StorageContract := by
  intro interface definitions shape a b heap left right output found header read_left read_right
    writable separate_left separate_right bounded
  exact ⟨helper_call_correct definitions a b heap left right output found header read_left read_right
      writable separate_left separate_right bounded,
    EncodedTensor.written_reads heap output (result a b), result_spec a b,
    EncodedTensor.written_frame heap output (result a b) shape.volume⟩

/-- Classification of every coordinate on the exact helper result heap.
No emitted runtime detector, interface failure policy or MISRA closure is
asserted here. This supplies the observation needed by a later detector loop. -/
def ClassificationContract : Prop :=
  ∀ {shape : Shape} (a b : Values shape) (heap : Heap) (output : Address),
    EncodedTensor.AllFinite (EncodedTensor.written heap output (result a b) shape.volume)
      output shape ↔ ∀ i : Fin shape.volume, Binary64.finiteProduct a[i] b[i]

theorem classification_correct : ClassificationContract := by
  intro shape a b heap output
  rw [EncodedTensor.allFinite_iff _ _ _ (EncodedTensor.written_reads heap output (result a b))]
  exact result_allFinite a b

def ArtifactContract (actual : String) : Prop :=
  actual = (function .mul).render ∧ Syntax.Denotes actual .mul ∧
    StorageContract ∧ ClassificationContract

theorem artifact_correct (actual : String) (printed : actual = (function .mul).render) :
    ArtifactContract actual :=
  ⟨printed, printed ▸ Syntax.render_denotes .mul, storage_correct, classification_correct⟩

end Rumoca.CTensor.MultiplicationTotal
