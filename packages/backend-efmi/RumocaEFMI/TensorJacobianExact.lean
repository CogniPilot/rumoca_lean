import RumocaC.SquareJacobianExact
import RumocaEFMI.TensorJacobianObservation

noncomputable section
namespace Rumoca.EFMI.JacobianExact
open CMemory CMemory.TensorView Rumoca.Tensor CTensor Solve.Tensor
open CTensor.SquareJacobianObservation CTensor.SquareJacobianExact
open TensorNumericalLinkage

/-- Exact finite AD matrix Reads and the mathematical derivative observation
are on the SAME heap returned under any saved caller in the ten-tree table.
RHS execution here is a finite Solve premise, NOT proof that DoStep executed it.
The dictionary is the actual eFMI backend interface. -/
theorem typed_helper_exact (unusedKernel : CSyntax.Program)
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
    CCalls.Typed.CallResult (program unusedKernel) SquareDiagonal.function.signature.name
      (Diagonal.argumentValues input output shape) heap (Diagonal.resultHeap heap output result) ∧
    Reads (Diagonal.resultHeap heap output result) output
      ((ArrayProfile.squareJacobianProgram shape).eval Finite.ops
        Binary64.positiveZero Binary64.one (ArrayProfile.environment state values)) ∧
    Observes (Diagonal.resultHeap heap output result) output state values ∧
    (∀ q, (∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ output.index i) →
      Diagonal.resultHeap heap output result q = heap q) := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨ran, matrixReads, observations, frame⟩ :=
    JacobianObservation.typed_helper_observations unusedKernel input output state values result heap
      separate reads adds writable bounded
  exact ⟨coefficients_from_rhs state values rhs result rhsExecuted adds, ran,
    (matrix_equal state values result adds) ▸ matrixReads, observations, frame⟩

end Rumoca.EFMI.JacobianExact
