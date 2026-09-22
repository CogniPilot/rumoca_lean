import RumocaC.TensorEncodedWriter
import RumocaC.TensorCalls
import RumocaC.TensorSyntax
import RumocaC.MultiplicationResults

/-! The existing tensor multiplication loop on all finite input encodings.
The output may contain infinities. The independent scalar specification and
full output/frame share the same heap; no finite-result assumption is used. -/
noncomputable section
namespace Rumoca.CTensor.MultiplicationTotal
open CTree CMemory CMemory.TensorView Rumoca.Tensor
open CMemory.EncodedTensor (Bits ReadsBits finiteBits)
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

def result (a b : Values shape) : Bits shape :=
  Tensor.Value.zipWith (fun x y => (Binary64.mulResult x y).encode) a b

/-- The target storage contains the prepared numerical result; the backend
does not own a different numerical interpretation. -/
theorem result_core (a b : Values shape) :
    result a b = Solve.Tensor.Numerical.encode (Solve.Tensor.Numerical.multiply a b) := by
  apply Tensor.Value.ext
  intro i hi
  simp only [result, Solve.Tensor.Numerical.encode, Solve.Tensor.Numerical.multiply,
    Tensor.Value.getElem_mapWith, Tensor.Value.getElem_zipWith]

theorem result_allFinite (a b : Values shape) :
    Solve.Tensor.Numerical.allFiniteBits (result a b) = true ↔
      ∀ i : Fin shape.volume, Binary64.finiteProduct a[i] b[i] := by
  rw [result_core, Solve.Tensor.Numerical.allFiniteBits_encode,
    Solve.Tensor.Numerical.multiply_allFinite_iff]

theorem result_get (a b : Values shape) (i : Nat) (hi : i < shape.volume) :
    (result a b)[i] = (Binary64.mulResult a[i] b[i]).encode :=
  Tensor.Value.getElem_zipWith _ _ _ hi

theorem result_spec (a b : Values shape) (i : Fin shape.volume) :
    Binary64.MultipliesResult a[i] b[i] (Float64.decode (result a b)[i]) := by
  simp only [Fin.getElem_fin, result_get, Float64.decode_encode]
  exact Binary64.mulResult_spec _ _

theorem result_finite (a b finite : Values shape)
    (multiplies : ∀ i : Fin shape.volume, Binary64.Multiplies a[i] b[i] finite[i]) :
    result a b = finiteBits finite := by
  apply Tensor.Value.ext
  intro i hi
  rw [result_get, EncodedTensor.finiteBits_get]
  have equal : Binary64.mulResult a[i] b[i] = .finite finite[i] :=
    (Binary64.mulResult_correct _ _ _).2 (multiplies ⟨i, hi⟩)
  rw [equal]
  rfl

variable [interface : CInterface]

theorem function_reaches (a b : Values shape) (heap : Heap) (left right output : Address)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (bounded : shape.volume < 2 ^ 64) (size_type : interface.types "size_t" = some .size) :
    Transition.Reaches CLoops.machine.step
      (.running (function .mul).body (parameters left right output shape.volume) parameterTypes heap)
      (.returned ⟨.void, EncodedTensor.written heap output (result a b) shape.volume⟩) := by
  apply EncodedWriter.writer_reaches (.bin .mul (indexed "left") (indexed "right"))
    (result a b) (parameters left right output shape.volume) parameterTypes heap output
    (by simp [parameters]) (by simp [parameters]) (by simp [parameters]) write_output bounded size_type
  intro i
  let env := CLoops.counterEnv (parameters left right output shape.volume) "k" i.val
  let before := EncodedTensor.written heap output (result a b) i.val
  have counter : env "k" = some (.integer i.val) := by simp [env, CLoops.counterEnv, CBody.bind]
  have leftEval := index_eval env before "left" left i.val
    (by simp [env, CLoops.counterEnv, CBody.bind, parameters]) counter
  have rightEval := index_eval env before "right" right i.val
    (by simp [env, CLoops.counterEnv, CBody.bind, parameters]) counter
  have leftRead := EncodedTensor.reads_written heap output left (result a b) a i.val separate_left read_left i
  have rightRead := EncodedTensor.reads_written heap output right (result a b) b i.val separate_right read_right i
  simp only [Fin.getElem_fin, result_get]
  exact CArithmetic.eval_mul CBody.legacyExpressions env _ before (indexed "left") (indexed "right")
    a[i] b[i] (leftEval.trans leftRead) (rightEval.trans rightRead)

theorem helper_call_reaches (definitions : CLoops.Calls.Definitions)
    (a b : Values shape) (heap : Heap) (left right output : Address) (stack : CLoops.Calls.Continuation)
    (found : definitions (function .mul).signature.name = some (function .mul))
    (header : HeaderTypes interface)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (function .mul).signature.name (argumentValues left right output shape.volume) heap stack)
      (.returning (EncodedTensor.written heap output (result a b) shape.volume) stack) := by
  have executed := function_reaches a b heap left right output read_left read_right write_output
    separate_left separate_right bounded header.size
  exact CLoops.Calls.call_reaches definitions _ _ heap _ (function .mul) _ _ stack found rfl
    (bind_parameters .mul left right output shape.volume header bounded) (bind_types .mul header) executed

theorem helper_call_correct (definitions : CLoops.Calls.Definitions)
    (a b : Values shape) (heap : Heap) (left right output : Address)
    (found : definitions (function .mul).signature.name = some (function .mul))
    (header : HeaderTypes interface)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling (function .mul).signature.name (argumentValues left right output shape.volume) heap .done)
      behavior ↔ behavior = .terminates (EncodedTensor.written heap output (result a b) shape.volume) := by
  have ran := helper_call_reaches definitions a b heap left right output .done found header
    read_left read_right write_output separate_left separate_right bounded
  exact (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

end Rumoca.CTensor.MultiplicationTotal
