import RumocaC.TensorSumPreflight
import RumocaC.TensorSumPreflightSyntax
import RumocaC.TensorOperationPreflightContract

/-! Actual-byte contract for the read-only sum preflight: the operation
preflight contract with the encoded total sums, and the finite-sum domain with
a real overflow witness. This does not certify invocation or failure handling
by a public method, nor the native compiler, floating environment or headers. -/
noncomputable section
namespace Rumoca.CTensor.SumPreflight
open CMemory CMemory.TensorView CMemory.EncodedTensor FinitePreflight

def ArtifactContract (actual : String) : Prop :=
  OperationContract "rumoca_tensor_add_finite" .add "+" result actual ∧
  ∀ (shape : Tensor.Shape) (a b : Values shape),
    (Solve.Tensor.Numerical.allFiniteBits (result a b) = true ↔
      ∀ i : Fin shape.volume,
        -Binary64.overflowUnits < Binary64.units a[i] + Binary64.units b[i] ∧
          Binary64.units a[i] + Binary64.units b[i] < Binary64.overflowUnits) ∧
    (Solve.Tensor.Numerical.allFiniteBits (result a b) = false ↔
      ∃ i : Fin shape.volume,
        Binary64.value a[i] + Binary64.value b[i] ≤ -Binary64.overflowValue ∨
          Binary64.overflowValue ≤ Binary64.value a[i] + Binary64.value b[i])

theorem artifact_correct (actual : String) (emitted : actual = function.render) :
    ArtifactContract actual :=
  ⟨operation_contract _ .add "+" result
      (fun interface _ a b heap left right read_left read_right =>
        @evaluates interface _ a b heap left right read_left read_right)
      Syntax.render_denotes actual emitted,
    fun _ a b => ⟨result_allFinite a b, result_overflow a b⟩⟩

end Rumoca.CTensor.SumPreflight
