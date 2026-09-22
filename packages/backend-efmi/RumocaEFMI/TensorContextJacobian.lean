import RumocaC.ContextCallResult
import RumocaEFMI.TensorNumericalFieldFree
import RumocaEFMI.TensorJacobianExact

/-! The actual scratch-free helper on the array-aware machine. Exact finite
AD and mathematical observations remain on one heap. No public-method claim. -/
noncomputable section
namespace Rumoca.EFMI.ContextJacobian
open CMemory CMemory.TensorView Rumoca.Tensor CTensor Solve.Tensor
open CTensor.SquareJacobianObservation CTensor.SquareJacobianExact
open TensorNumericalLinkage

/-- The declaration/object maps may describe array-bearing public callers.
Only the actual seven helper bodies are required to be field-free, and their
syntax certificates discharge that fact internally. Saved callers are arbitrary.
The numerical interface is the actual eFMI backend dictionary. -/
theorem helper_exact (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (unusedKernel : CSyntax.Program)
    (input output : Address) (state values rhs result : Values shape) (heap : Heap)
    (rhsExecuted : Finite.Executes (ArrayProfile.squareProgram shape)
      (ArrayProfile.environment state values) rhs)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    letI : CInterface := NumericalInterface.interface
    Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state values) result ∧
    CContextMachine.CallResult (CContextMachine.declared declarations objects)
      (program unusedKernel) SquareDiagonal.function.signature.name
      (Diagonal.argumentValues input output shape) heap (Diagonal.resultHeap heap output result) ∧
    Reads (Diagonal.resultHeap heap output result) output
      ((ArrayProfile.squareJacobianProgram shape).eval Finite.ops
        Binary64.positiveZero Binary64.one (ArrayProfile.environment state values)) ∧
    Observes (Diagonal.resultHeap heap output result) output state values ∧
    (∀ q, (∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ output.index i) →
      Diagonal.resultHeap heap output result q = heap q) := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨ran, matrixReads, observes, frame⟩ :=
    JacobianObservation.helper_observations input output state values result heap
      separate reads adds writable bounded
  have contextual := CContextMachine.loop_call_result_context declarations objects
    (program unusedKernel) definitions (numerical_in_actual unusedKernel)
    TensorNumericalFieldFree.definition_body ((ran _).2 rfl)
  exact ⟨coefficients_from_rhs state values rhs result rhsExecuted adds, contextual,
    (matrix_equal state values result adds) ▸ matrixReads, observes, frame⟩

end Rumoca.EFMI.ContextJacobian
