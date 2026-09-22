import RumocaFMI3.TensorAcceptedLinked
import RumocaFMI3.TensorHeader
import RumocaFMI3.TensorNumericalEvents

/-! Accepted public calls on the actual FMI runtime dictionary and the same
adapter/numerical tree table. Header meanings, step/helper lookups, restricted
libraries and reachable helper resolution are derived, not caller obligations.
Native correspondence and total finite-arithmetic coverage remain separate. -/
noncomputable section
namespace Rumoca.FMI3.TensorAcceptedRuntime
open CTree CMemory
set_option autoImplicit false
variable {source : AST.Model} {shape : Tensor.Shape}

def Contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) : Prop :=
  ∀ (header : CFenv.Header) (objects : StaticFactory.Objects) (literals : CLiteralAddresses),
    cond m.hasOutput
      (TensorAcceptedLinked.ExecutionOutput shape header
        (RuntimeEnvironment.interface header objects literals)
        (TensorHeader.runtime_tensor header objects literals)
        (TensorFunctions.squareLinkedProgram model m sigs))
      (TensorAcceptedLinked.ExecutionFree shape header
        (RuntimeEnvironment.interface header objects literals)
        (TensorHeader.runtime_tensor header objects literals)
        (TensorFunctions.squareLinkedProgram model m sigs))

theorem contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (stepMember : StepEntry.signature ∈ sigs)
    (unique : ((TensorFunctions.functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (covered : PublicAPI.Covered sigs) : Contract model m sigs := by
  intro header objects literals
  have defined : (TensorFunctions.squareLinkedProgram model m sigs).definitions "fmi3DoStep" =
      some (.tree (TensorDoStep.function shape m.hasOutput)) := by
    change (TensorFunctions.squareLinkedProgram model m sigs).definitions StepEntry.signature.name =
      some (.tree (TensorFunctions.tensorFunction model m StepEntry.signature))
    exact TensorFunctions.square_linked_adapter model m sigs unique covered _
      (List.mem_append_right _ (List.mem_map.mpr ⟨StepEntry.signature, stepMember, rfl⟩))
  have linked := TensorFunctions.linked_numerical_covered model m sigs unique covered
  cases output : m.hasOutput
  · simp only [cond_false]
    intro E
    exact TensorAcceptedLinked.execution_free shape header _
      (TensorHeader.runtime_tensor header objects literals)
      (TensorHeader.runtime_step_types header objects literals)
      (TensorHeader.runtime_binary header objects literals)
      (TensorHeader.runtime_fill header objects literals)
      (TensorHeader.runtime_nearest header objects literals)
      (TensorKernel.runtime_helpers_clear header objects literals) _ linked
      (by simpa only [output] using defined)
  · simp only [cond_true]
    intro E
    exact TensorAcceptedLinked.execution_output shape header _
      (TensorHeader.runtime_tensor header objects literals)
      (TensorHeader.runtime_step_types header objects literals)
      (TensorHeader.runtime_binary header objects literals)
      (TensorHeader.runtime_fill header objects literals)
      (TensorHeader.runtime_nearest header objects literals)
      (TensorKernel.runtime_helpers_clear header objects literals) _ linked
      (by simpa only [output] using defined)

end Rumoca.FMI3.TensorAcceptedRuntime
