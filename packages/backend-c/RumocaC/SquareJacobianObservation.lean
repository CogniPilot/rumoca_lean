import RumocaC.TensorSquareDiagonal

/-! Scratch proof bridge from the executed scratch-free materializer to the
mathematical Jacobian of the prepared AD program. No emitter/contract changes. -/
noncomputable section
namespace Rumoca.CTensor.SquareJacobianObservation
open CMemory CMemory.TensorView Rumoca.Tensor

def mathematical (state input : Values shape) : ArrayProfile.Jacobian shape :=
  ((ArrayProfile.squareJacobianProgram shape).eval AD.realOps 0 1
    (ArrayProfile.environment (state.mapWith Binary64.value)
      (input.mapWith Binary64.value))).toMatrix

theorem mathematical_eq (state input : Values shape) :
    mathematical state input = AD.squareJacobian (fun i => Binary64.value input[i]) := by
  rw [mathematical, ArrayProfile.square_jacobian_eval]
  simp only [Fin.getElem_fin, Value.getElem_mapWith]

theorem mathematical_derivative (state input : Values shape) :
    ArrayProfile.JacobianOf (fun x => BinaryOp.denote AD.realOps .mul x x)
      (fun i => Binary64.value input[i]) (mathematical state input) :=
  (ArrayProfile.JacobianOf.square_iff _ _).2 (mathematical_eq state input)

/-- Every stored coordinate, including exact off-diagonal zero, is nearest to
the corresponding entry of the mathematical AD Jacobian. Signed-zero encodings
are not identified merely because their real values coincide. -/
theorem matrix_nearest (state input result : Values shape)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds input[i] input[i] (.finite result[i]))
    (i j : Fin shape.volume) (candidate : Binary64.Value) :
    |Binary64.value (Diagonal.matrix result)[matrixIndex (i, j)] -
        mathematical state input i j| ≤
      |Binary64.value candidate - mathematical state input i j| := by
  rw [SquareDiagonal.matrix_diagonal_nearest, mathematical_eq]
  by_cases same : i = j
  · subst j
    simpa [AD.squareJacobian, Matrix.diagonal, two_mul] using
      SquareDiagonal.diagonal_nearest input result adds i candidate
  · have zero_value : Binary64.value Binary64.positiveZero = 0 := by
      simp only [Binary64.value,
        show Binary64.units Binary64.positiveZero = 0 from rfl, Int.cast_zero, zero_div]
    simp only [same, if_false, AD.squareJacobian, Matrix.diagonal, Matrix.of_apply,
      zero_value, sub_zero, abs_zero]
    exact abs_nonneg _

/-- A heap observation uses the very matrix produced by this execution, not a
second existential heap or a hypothetical coefficient-buffer execution. -/
def Observes (heap : Heap) (output : Address) (state input : Values shape) : Prop :=
  ArrayProfile.JacobianOf (fun x => BinaryOp.denote AD.realOps .mul x x)
      (fun i => Binary64.value input[i]) (mathematical state input) ∧
  ∀ i j : Fin shape.volume, ∃ stored : Binary64.Value,
    load heap (output.index (matrixIndex (i, j)).val) = some (.finite stored) ∧
    ∀ candidate : Binary64.Value,
      |Binary64.value stored - mathematical state input i j| ≤
        |Binary64.value candidate - mathematical state input i j|

theorem result_observes (heap : Heap) (output : Address) (state input result : Values shape)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds input[i] input[i] (.finite result[i])) :
    Observes (Diagonal.resultHeap heap output result) output state input := by
  refine ⟨mathematical_derivative state input, ?_⟩
  intro i j
  exact ⟨(Diagonal.matrix result)[matrixIndex (i, j)],
    SquareDiagonal.output_reads heap output result (matrixIndex (i, j)),
    matrix_nearest state input result adds i j⟩

section
variable [interface : CInterface]

/-- Ordinary helper execution, exact matrix reads and its mathematical AD
observation share one final heap. All existing finite/storage premises remain. -/
theorem helper_contract (definitions : CLoops.Calls.Definitions)
    (input output : Address) (state values result : Values shape) (heap : Heap)
    (found : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i]))
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    (∀ behavior, (CLoops.Calls.machine definitions).Behaves
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues input output shape) heap .done) behavior ↔
      behavior = .terminates (Diagonal.resultHeap heap output result)) ∧
    Reads (Diagonal.resultHeap heap output result) output (Diagonal.matrix result) ∧
    Observes (Diagonal.resultHeap heap output result) output state values ∧
    (∀ q, (∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ output.index i) →
      Diagonal.resultHeap heap output result q = heap q) :=
  ⟨SquareDiagonal.helper_call_correct definitions input output result values heap
      found fillDefined header fillHeader separate reads adds writable bounded,
    SquareDiagonal.output_reads heap output result,
    result_observes heap output state values result adds,
    SquareDiagonal.output_frame heap output result⟩
end
end Rumoca.CTensor.SquareJacobianObservation
