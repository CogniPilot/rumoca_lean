import RumocaC.TensorProductPreflightCalls
import RumocaC.TensorProductPreflightSyntax
import RumocaCore.Array.Numerical

/-! Actual-byte contract for the read-only product preflight. Execution and
the independent finite-product domain are required together. The square
specialization gives the prepared Solve execution boundary and a real overflow
witness. This does not yet certify invocation or failure handling by a public
FMI/eFMI method, nor the native compiler, floating environment or headers. -/
noncomputable section
namespace Rumoca.CTensor.ProductPreflight
open CMemory CMemory.TensorView CMemory.EncodedTensor

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
  actual = function.render ∧ Syntax.Denotes actual ∧
  (∀ (interface : CInterface) (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program) (shape : Tensor.Shape)
    (a b : Values shape) (heap : Heap) (left right : Option Address),
    HeaderTypes interface → p.definitions function.signature.name = some (.tree function) →
    FiniteScan.Readable heap left (finiteBits a) → FiniteScan.Readable heap right (finiteBits b) →
    shape.volume < 2 ^ 64 →
    (∀ stack, Transition.Reaches
        (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).step
        (.calling function.signature.name (argumentValues left right shape.volume) heap stack)
        (.returning
          (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b))) heap stack)) ∧
    (∀ behavior,
      (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).Behaves
        (.calling function.signature.name (argumentValues left right shape.volume) heap .done) behavior ↔
        behavior = .terminates
          ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)), heap⟩) ∧
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b) = true ↔
      ∀ i : Fin shape.volume, Binary64.finiteProduct a[i] b[i])) ∧
  (∀ (shape : Tensor.Shape) (state input : Values shape),
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = true ↔
      ∃ result, Solve.Tensor.Finite.Executes (ArrayProfile.squareProgram shape)
        (ArrayProfile.environment state input) result) ∧
    (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result input input) = false ↔
      ∃ i : Fin shape.volume,
        Binary64.overflowValue ≤ Binary64.value input[i] * Binary64.value input[i]))

theorem artifact_correct (actual : String) (emitted : actual = function.render) :
    ArtifactContract actual := by
  refine ⟨emitted, emitted ▸ Syntax.render_denotes, ?_, ?_⟩
  · intro interface declarations objects p shape a b heap left right header found read_left read_right bounded
    letI : CInterface := interface
    exact ⟨fun stack => call_reaches declarations objects p a b heap left right stack found header
        read_left read_right bounded,
      call_correct declarations objects p a b heap left right found header read_left read_right bounded,
      MultiplicationTotal.result_allFinite a b⟩
  · intro shape state input
    exact ⟨square_finite_execution state input, square_overflow input⟩

end Rumoca.CTensor.ProductPreflight
