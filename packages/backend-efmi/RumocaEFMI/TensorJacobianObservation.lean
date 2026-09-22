import RumocaC.SquareJacobianObservation
import RumocaEFMI.TensorNumericalLinkage

noncomputable section
namespace Rumoca.EFMI.JacobianObservation
open CMemory CMemory.TensorView Rumoca.Tensor CTensor
open CTensor.SquareJacobianObservation
open TensorNumericalLinkage

/-- The actual seven-tree numerical table discharges all helper lookup/header
premises, under the actual backend interface. Storage and finite Adds remain. -/
theorem helper_observations
    (input output : Address) (state values result : Values shape) (heap : Heap)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    letI : CInterface := NumericalInterface.interface
    (∀ behavior, (CLoops.Calls.machine definitions).Behaves
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues input output shape) heap .done) behavior ↔
      behavior = .terminates (Diagonal.resultHeap heap output result)) ∧
    Reads (Diagonal.resultHeap heap output result) output (Diagonal.matrix result) ∧
    Observes (Diagonal.resultHeap heap output result) output state values ∧
    (∀ q, (∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ output.index i) →
      Diagonal.resultHeap heap output result q = heap q) := by
  letI : CInterface := NumericalInterface.interface
  exact helper_contract definitions input output state values result heap
    square_diagonal_defined fill_defined NumericalInterface.binary_header
    NumericalInterface.fill_header separate reads adds writable bounded

/-- The same helper result is usable under any saved caller of the actual
ten-tree typed program, including all exact reads, AD observations and frames.
This still does not assert evaluation of a public method's array arguments. -/
theorem typed_helper_observations (unusedKernel : CSyntax.Program)
    (input output : Address) (state values result : Values shape) (heap : Heap)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    letI : CInterface := NumericalInterface.interface
    CCalls.Typed.CallResult (program unusedKernel) SquareDiagonal.function.signature.name
      (Diagonal.argumentValues input output shape) heap (Diagonal.resultHeap heap output result) ∧
    Reads (Diagonal.resultHeap heap output result) output (Diagonal.matrix result) ∧
    Observes (Diagonal.resultHeap heap output result) output state values ∧
    (∀ q, (∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ output.index i) →
      Diagonal.resultHeap heap output result q = heap q) := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨ran, observations⟩ := helper_observations input output state values result heap
    separate reads adds writable bounded
  exact ⟨CCalls.Typed.loop_call_result (program unusedKernel) definitions
    (numerical_in_actual unusedKernel) ((ran _).2 rfl), observations⟩

end Rumoca.EFMI.JacobianObservation
