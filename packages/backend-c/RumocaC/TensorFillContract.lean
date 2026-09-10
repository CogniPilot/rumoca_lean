import RumocaC.TensorFillSyntax
import RumocaC.TensorFillProofs

/-! Actual fill-helper text, ordinary call execution, exact output values and
the complete heap frame. The source grammar is unchanged; array production
admission still requires whole-program storage and FMI artifact composition. -/
noncomputable section
namespace Rumoca.CTensor.Fill
open CMemory CMemory.TensorView

def ArtifactContract (source : String) : Prop :=
  Syntax.Denotes source ∧
  ∀ (interface : CInterface) (shape : Tensor.Shape) (value : Binary64.Value)
    (output : Address) (heap : Heap) (definitions : CLoops.Calls.Definitions),
    HeaderTypes interface → definitions function.signature.name = some function →
    Writable heap output shape.volume → shape.volume < 2 ^ 64 →
    (Reads (written heap output (Tensor.Value.fill shape value) shape.volume) output (Tensor.Value.fill shape value) ∧
      (∀ q, (∀ i < shape.volume, q ≠ output.index i) →
        written heap output (Tensor.Value.fill shape value) shape.volume q = heap q) ∧
      ∀ behavior, (@CLoops.Calls.machine interface definitions).Behaves
        (.calling function.signature.name (argumentValues value output shape.volume) heap .done) behavior ↔
        behavior = .terminates (written heap output (Tensor.Value.fill shape value) shape.volume))

theorem artifact_correct (source : String) (emitted : source = function.render) : ArtifactContract source := by
  refine ⟨emitted ▸ Syntax.render_denotes, ?_⟩
  intro interface shape value output heap definitions header found writable bounded
  letI : CInterface := interface
  exact ⟨written_reads _ _ _, written_frame _ _ _ _,
    helper_call_correct definitions shape value output heap found header writable bounded⟩

end Rumoca.CTensor.Fill
