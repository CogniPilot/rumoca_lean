import RumocaFMI3.TensorDoStep

/-! Explicit-target accepted product retaining every legacy contract field.
The generic canonical whole-call proofs live in TensorDoStep. -/
noncomputable section
namespace Rumoca.FMI3.TensorDoStep
open CTree CMemory

section
variable [static : StaticLiterals]

/-- Explicit transition product: retain every old field and additionally require
restricted accepted execution in the specified target. The two interfaces are
not equated. Production dictionary cutover requires rebuilding dependents. -/
structure ContractFor (shape : Tensor.Shape) (hasOutput : Bool) (header : CFenv.Header)
    (text : String) (target : CInterface) (fenv : TensorFenv target) : Prop extends Contract shape hasOutput header text where
  executionFor : cond hasOutput (ExecutionOutputFor shape header target fenv) (ExecutionFreeFor shape header target fenv)

theorem contract_for (shape : Tensor.Shape) (hasOutput : Bool) (header : CFenv.Header)
    (target : CInterface) (fenv : TensorFenv target)
    (nearest : target.constants "FE_TONEAREST" = some (.integer header.nearest)) :
    ContractFor shape hasOutput header (function shape hasOutput).render target fenv := by
  refine ⟨contract shape hasOutput header, ?_⟩
  cases hasOutput
  · exact execution_free_for shape header target fenv nearest
  · exact execution_output_for shape header target fenv nearest

end

end Rumoca.FMI3.TensorDoStep
