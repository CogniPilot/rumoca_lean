import RumocaC.TensorProductPreflightCalls
import RumocaC.TensorProductPreflightSyntax
import RumocaC.TensorOperationPreflightContract
import RumocaCore.Array.Numerical

/-! Actual-byte contract for the read-only product preflight. Execution and
the independent finite-product domain are required together. The square
specialization gives the prepared Solve execution boundary and a real overflow
witness. This does not yet certify invocation or failure handling by a public
FMI/eFMI method, nor the native compiler, floating environment or headers. -/
noncomputable section
namespace Rumoca.CTensor.ProductPreflight
open CMemory CMemory.TensorView CMemory.EncodedTensor FinitePreflight

theorem square_finite_execution (state input : Values shape) :
    Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = true ↔
      ∃ result, Solve.Tensor.Finite.Executes (ArrayProfile.squareProgram shape)
        (ArrayProfile.environment state input) result := by
  rw [MultiplicationTotal.result_core]
  exact ArrayProfile.square_detection_finite_execution state input

theorem square_overflow (input : Values shape) :
    Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = false ↔
      ∃ i : Fin shape.volume,
        Binary64.overflowValue ≤ Binary64.value input[i] * Binary64.value input[i] := by
  rw [MultiplicationTotal.result_core]
  exact ArrayProfile.square_detection_overflow input

def ArtifactContract (actual : String) : Prop :=
  OperationContract "rumoca_tensor_mul_finite" .mul "*" MultiplicationTotal.result actual ∧
  (∀ (shape : Tensor.Shape) (a b : Values shape),
    Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b) = true ↔
      ∀ i : Fin shape.volume, Binary64.finiteProduct a[i] b[i]) ∧
  (∀ (shape : Tensor.Shape) (state input : Values shape),
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = true ↔
      ∃ result, Solve.Tensor.Finite.Executes (ArrayProfile.squareProgram shape)
        (ArrayProfile.environment state input) result) ∧
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = false ↔
      ∃ i : Fin shape.volume,
        Binary64.overflowValue ≤ Binary64.value input[i] * Binary64.value input[i]))

theorem artifact_correct (actual : String) (emitted : actual = function.render) :
    ArtifactContract actual :=
  ⟨operation_contract _ .mul "*" MultiplicationTotal.result
      (fun interface _ a b heap left right read_left read_right =>
        @evaluates interface _ a b heap left right read_left read_right)
      Syntax.render_denotes actual emitted,
    fun _ a b => MultiplicationTotal.result_allFinite a b,
    fun _ state input => ⟨square_finite_execution state input, square_overflow input⟩⟩

end Rumoca.CTensor.ProductPreflight
