import RumocaC.TensorSquareDiagonalTotal

/-! Actual-text contract for the existing scratch-free Jacobian helper.
Finite input encodings have a total finite-or-infinite output; storage, shape
bounds and function/header bindings remain explicit. -/
namespace Rumoca.CTensor.SquareDiagonal.Total
open CMemory CMemory.TensorView Rumoca.Tensor

def StorageContract : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions) {shape : Shape}
    (input output : Address) (values : Values shape) (heap : Heap),
  definitions function.signature.name = some function →
  definitions Fill.function.signature.name = some Fill.function →
  CTensor.HeaderTypes interface → Fill.HeaderTypes interface →
  Diagonal.Separate output input shape → Reads heap input values →
  Writable heap output (matrixShape shape.volume shape.volume).volume →
  (matrixShape shape.volume shape.volume).volume < 2 ^ 64 →
    (∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling function.signature.name (Diagonal.argumentValues input output shape) heap .done) behavior ↔
        behavior = .terminates (EncodedDiagonal.resultHeap heap output (result values))) ∧
    EncodedDiagonal.ReadsBits (EncodedDiagonal.resultHeap heap output (result values)) output
      (EncodedDiagonal.matrix (result values)) ∧
    (∀ i : Fin shape.volume,
      Binary64.Adds values[i] values[i] (Float64.decode (result values)[i])) ∧
    (∀ q, (∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ output.index i) →
      EncodedDiagonal.resultHeap heap output (result values) q = heap q)

theorem storage_correct : StorageContract := by
  intro interface definitions shape input output values heap found fillDefined header fillHeader
    separate reads writable bounded
  exact ⟨helper_call_correct definitions input output values heap found fillDefined header fillHeader
      separate reads writable bounded,
    EncodedDiagonal.result_reads heap output (result values), result_spec values,
    EncodedDiagonal.result_frame heap output (result values)⟩

def ArtifactContract (actual : String) : Prop :=
  actual = function.render ∧ StorageContract

theorem artifact_correct (actual : String) (printed : actual = function.render) :
    ArtifactContract actual := ⟨printed, storage_correct⟩

end Rumoca.CTensor.SquareDiagonal.Total
