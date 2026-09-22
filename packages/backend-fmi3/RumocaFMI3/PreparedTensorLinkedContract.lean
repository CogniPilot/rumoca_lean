import RumocaFMI3.PreparedStepContract
import RumocaFMI3.TensorLinkedProgram

/-! Prepared rejection calls use the same adapter/numerical tree table. -/
noncomputable section
namespace Rumoca.FMI3.PreparedStep
open CTree CMemory CLiteral CBody
set_option autoImplicit false

theorem tensor_linked_contract {source : AST.Model} {shape : Tensor.Shape}
    (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (covered : PublicAPI.Covered sigs) :
    TensorContractFor model m sigs (TensorFunctions.squareLinkedProgram model m sigs) := by
  apply tensor_contract_for model m sigs stepMember (TensorFunctions.squareLinkedProgram model m sigs)
  · change (TensorFunctions.squareLinkedProgram model m sigs).definitions StepEntry.signature.name =
      some (.tree (TensorFunctions.tensorFunction model m StepEntry.signature))
    exact TensorFunctions.square_linked_adapter model m sigs unique covered _
      (List.mem_append_right _ (List.mem_map.mpr ⟨StepEntry.signature, stepMember, rfl⟩))
  · exact TensorFunctions.square_linked_adapter model m sigs unique covered Runtime.helpers[0]
      (List.mem_append_left _ (by simp [TensorFunctions.helpers]))

end Rumoca.FMI3.PreparedStep
