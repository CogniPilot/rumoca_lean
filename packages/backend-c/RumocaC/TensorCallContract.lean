import RumocaC.TensorContract
import RumocaC.TensorCalls

/-! The actual-file contract retains the prior body/finite/frame guarantee
and additionally covers entry, parameter conversions, fresh scope and return
of an ordinary C call. The definition table must bind the helper name to the
tree denoted by this file. Native linkage/ABI and allocation are not assumed
to be verified by this authored function-call semantics. -/
noncomputable section
namespace Rumoca.CTensor
open CMemory CMemory.TensorView Solve.Tensor

def CallArtifactContract (source : String) (op : Tensor.BinaryOp) : Prop :=
  ArtifactContract source op ∧
  ∀ (interface : CInterface) (shape : Tensor.Shape) (a b result : Values shape)
    (heap : Heap) (left right output : Address) (definitions : CLoops.Calls.Definitions),
    HeaderTypes interface → definitions (function op).signature.name = some (function op) →
    Reads heap left a → Reads heap right b → Writable heap output shape.volume →
    Separate output left shape.volume → Separate output right shape.volume →
    Finite.Pointwise op a b result → shape.volume < 2 ^ 64 →
    (Reads (written heap output result shape.volume) output result ∧
      (∀ q, (∀ i < shape.volume, q ≠ output.index i) →
        written heap output result shape.volume q = heap q) ∧
      ∀ behavior, (@CLoops.Calls.machine interface definitions).Behaves
        (.calling (function op).signature.name (argumentValues left right output shape.volume) heap .done)
        behavior ↔ behavior = .terminates (written heap output result shape.volume))

theorem call_artifact_correct (op : Tensor.BinaryOp) (source : String)
    (emitted : source = (function op).render) : CallArtifactContract source op := by
  refine ⟨artifact_correct op source emitted, ?_⟩
  intro interface shape a b result heap left right output definitions header found
    hl hr hw sl sr finite bounded
  letI : CInterface := interface
  exact ⟨written_reads _ _ _, written_frame _ _ _ _,
    helper_call_correct definitions op a b result heap left right output
      found header hl hr hw sl sr finite bounded⟩

end Rumoca.CTensor
