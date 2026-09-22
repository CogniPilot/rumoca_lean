import RumocaC.TensorEncodedDiagonal
import RumocaC.TensorSquareDiagonal

/-! Total encoded result of the square-Jacobian helper on finite inputs.
Overflow produces the specified infinity encoding; no finite-output premise is
assumed. This is authored C/IEEE result semantics, not exception-flag, trapping,
native-toolchain, or real-valued AD correctness for overflowing operations. -/
noncomputable section
namespace Rumoca.CTensor.SquareDiagonal.Total
open CTree CMemory CMemory.TensorView Rumoca.Tensor
open EncodedDiagonal
open Diagonal (zeroHeap position locals signatureParameters arguments
  offset_step offset_eval position_bounded counter_bounds)
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

def result (values : Values shape) : Bits shape :=
  ⟨values.data.map (fun x => (Binary64.addResult x x).encode)⟩

theorem result_get (values : Values shape) (i : Nat) (hi : i < shape.volume) :
    (result values)[i] = (Binary64.addResult values[i] values[i]).encode :=
  Vector.getElem_map _ _

/-- Independent numerical relation for each stored diagonal encoding, including
both overflow signs and the signed-zero-aware finite branch. -/
theorem result_spec (values : Values shape) (i : Fin shape.volume) :
    Binary64.Adds values[i] values[i] (Float64.decode (result values)[i]) := by
  simp only [Fin.getElem_fin, result_get, Float64.decode_encode]
  exact Binary64.addResult_spec _ _

theorem result_no_nan (values : Values shape) (i : Fin shape.volume) :
    Float64.decode (result values)[i] ≠ .nan := by
  simp only [Fin.getElem_fin, result_get, Float64.decode_encode]
  exact Binary64.addResult_no_nan _ _

/-- On the old finite domain this is the same final heap, not another memory
model with merely matching real-valued observations. -/
theorem result_finite (values finite : Values shape)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite finite[i])) :
    result values = finiteBits finite := by
  apply Tensor.Value.ext
  intro i hi
  rw [result_get, finiteBits_get]
  have equal := (Binary64.addResult_correct _ _ _).2 (adds ⟨i, hi⟩)
  simp only [Fin.getElem_fin] at equal
  rw [equal]
  rfl

variable [interface : CInterface]

theorem copy_step (output input : Address) (values : Values shape) (heap : Heap)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (i : Fin shape.volume) (rest : List Stmt) :
    CLoops.next (.running (operation ++ rest)
      (CLoops.counterEnv (locals input output shape i.val) "k" i.val) Diagonal.localTypes
      (scatter (zeroHeap heap output shape) output (result values) i.val)) =
      some (.running (.assign (.id "offset") (.bin .add (.id "offset") (.id "stride")) :: rest)
        (CLoops.counterEnv (locals input output shape i.val) "k" i.val) Diagonal.localTypes
        (scatter (zeroHeap heap output shape) output (result values) (i.val + 1))) := by
  set env := CLoops.counterEnv (locals input output shape i.val) "k" i.val with henv
  set H := scatter (zeroHeap heap output shape) output (result values) i.val with hH
  have coeffPtr : env "coeff" = some (.pointer (some input)) := by
    simp [henv, CLoops.counterEnv, locals, Diagonal.parameters, Lowering.Arguments.locals,
      signatureParameters, arguments, CBody.bind]
  have counter : env "k" = some (.integer i.val) := by
    simp [henv, CLoops.counterEnv, CBody.bind]
  have coeffLoad : load H (input.index i.val) = some (.finite values[i]) :=
    EncodedDiagonal.coeff_reads heap output input (result values) values i.val separate reads i
  have coeffEval : CBody.eval env H (indexed "coeff") = some (.finite values[i]) :=
    (Rumoca.CTensor.index_eval env H "coeff" input i.val coeffPtr counter).trans coeffLoad
  have rhs : CLoops.eval env Diagonal.localTypes H (.bin .add (indexed "coeff") (indexed "coeff")) =
      some (.float64 (result values)[i]) := by
    rw [Fin.getElem_fin, result_get]
    have unfold : CLoops.eval env Diagonal.localTypes H (.bin .add (indexed "coeff") (indexed "coeff")) =
        (CBody.eval env H (indexed "coeff")).bind
          (fun x => (CBody.eval env H (indexed "coeff")).bind (fun y => CArithmetic.floatAdd x y)) := rfl
    rw [unfold, coeffEval]
    simp only [Option.bind_some]
    exact CArithmetic.add_result _ _
  have target : CBody.lvalue env H (.index (.id "out") (.id "offset")) =
      some (output.index (position shape i.val)) := by
    simp [henv, CBody.lvalue, CBody.lvalueWith, CBody.evalWith, CBody.resolve, CLoops.counterEnv,
      locals, Diagonal.parameters, Lowering.Arguments.locals, signatureParameters, arguments,
      CBody.bind, CMemory.Value.address]
  have stored := scatter_store_next (zeroHeap heap output shape) output (result values)
    (Diagonal.zero_writable heap output shape) i
  rw [← hH] at stored
  change CBody.legacyExpressions.address env H (.index (.id "out") (.id "offset")) =
    some (output.index (position shape i.val)) at target
  simp only [operation, List.cons_append, List.nil_append, CLoops.next, CLoops.nextWith,
    rhs, target, stored, bind, Option.bind_some, pure]

theorem loop_reaches (input output : Address) (values : Values shape) (heap : Heap)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches CLoops.machine.step
      (.running [CLoops.loop "k" (.id "count") operation, .ret none]
        (CLoops.counterEnv (locals input output shape 0) "k" 0) Diagonal.localTypes (zeroHeap heap output shape))
      (.returned ⟨.void, resultHeap heap output (result values)⟩) := by
  have repeated := CLoops.loop_reaches "k" (.id "count") operation [.ret none]
    (locals input output shape) Diagonal.localTypes (scatter (zeroHeap heap output shape) output (result values))
    shape.volume (by simp [Diagonal.localTypes, CLoops.bindType]) (counter_bounds shape bounded).1
    (by simp [operation, CLoops.noDeclarations])
    (by
      intro i hi
      simp [CBody.eval, CBody.evalWith, CBody.resolve, CLoops.counterEnv, locals, Diagonal.parameters,
        Lowering.Arguments.locals, signatureParameters, arguments, CBody.bind])
    (by
      intro i hi
      exact .next (copy_step output input values heap separate reads ⟨i, hi⟩ _)
        (.next (offset_step input output shape _ i (position_bounded shape bounded (i + 1) (by omega))
          _ (offset_eval input output shape _ bounded i hi)) (.refl _)))
  exact repeated.trans (.next rfl (.refl _))

theorem tail_reaches (input output : Address) (values : Values shape) (heap : Heap)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (sizeType : interface.types "size_t" = some .size) :
    Transition.Reaches CLoops.machine.step
      (.running tail (Diagonal.parameters input output shape) Diagonal.parameterTypes (zeroHeap heap output shape))
      (.returned ⟨.void, resultHeap heap output (result values)⟩) :=
  (SquareDiagonal.initialize_reaches input output shape heap bounded sizeType).trans
    (loop_reaches input output values heap separate reads bounded)

theorem function_reaches (definitions : CLoops.Calls.Definitions)
    (input output : Address) (values : Values shape) (heap : Heap) (stack : CLoops.Calls.Continuation)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : Fill.HeaderTypes interface)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running function.body (Diagonal.parameters input output shape) Diagonal.parameterTypes heap) stack)
      (.body (.returned ⟨.void, resultHeap heap output (result values)⟩) stack) := by
  have filled := Fill.invoke_reaches definitions (matrixShape shape.volume shape.volume)
    Binary64.positiveZero output heap (CAlgorithm.literal .zero) (.id "out") (.id "cells")
    (Diagonal.parameters input output shape) Diagonal.parameterTypes tail stack fillDefined header
    (by simp [Diagonal.parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind, Fill.function])
    (Fill.literal_eval .zero _ _ header.scalar)
    (by simp [CBody.eval, CBody.evalWith, CBody.resolve, Diagonal.parameters, Lowering.Arguments.locals,
      signatureParameters, arguments, CBody.bind])
    (by simp [CBody.eval, CBody.evalWith, CBody.resolve, Diagonal.parameters, Lowering.Arguments.locals,
      signatureParameters, arguments, CBody.bind]) writable bounded
  exact filled.trans (CLoops.Calls.body_reaches definitions
    (tail_reaches input output values heap separate reads bounded header.size) stack)

theorem helper_call_reaches (definitions : CLoops.Calls.Definitions)
    (input output : Address) (values : Values shape) (heap : Heap) (stack : CLoops.Calls.Continuation)
    (found : definitions function.signature.name = some function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling function.signature.name (Diagonal.argumentValues input output shape) heap stack)
      (.returning (resultHeap heap output (result values)) stack) := by
  have entered : (CLoops.Calls.machine definitions).step
      (.calling function.signature.name (Diagonal.argumentValues input output shape) heap stack)
      (.body (.running function.body (Diagonal.parameters input output shape) Diagonal.parameterTypes heap) stack) := by
    simp only [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith, found,
      show function.signature.result = "void" from rfl, ne_eq, not_true_eq_false, ↓reduceIte,
      show function.signature.parameters = Diagonal.function.signature.parameters from rfl,
      Diagonal.bind_parameters input output shape header bounded, Diagonal.bind_types header,
      bind, Option.bind_some, pure]
  exact .next entered ((function_reaches definitions input output values heap stack fillDefined fillHeader
    separate reads writable bounded).trans (.next
      (by simp [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith]) (.refl _)))

theorem helper_call_correct (definitions : CLoops.Calls.Definitions)
    (input output : Address) (values : Values shape) (heap : Heap)
    (found : definitions function.signature.name = some function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (separate : Diagonal.Separate output input shape) (reads : Reads heap input values)
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling function.signature.name (Diagonal.argumentValues input output shape) heap .done) behavior ↔
      behavior = .terminates (resultHeap heap output (result values)) := by
  have ran := helper_call_reaches definitions input output values heap .done found fillDefined header
    fillHeader separate reads writable bounded
  exact (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

end Rumoca.CTensor.SquareDiagonal.Total
