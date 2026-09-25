import RumocaC.TensorProductPreflightCode
import RumocaC.TensorOperationPreflight
import RumocaC.TensorMultiplicationTotal

/-! A preflight of prepared tensor multiplication, including finite-input
overflow, underflow and signed zero. Its result is the Solve classifier of the
same encoded result produced by the existing multiplication helper. Evaluation
preserves the entire heap, requires no writable storage or separation, and
allows null inputs exactly when no coordinate is visited. -/
noncomputable section
namespace Rumoca.CTensor.ProductPreflight
open CTree CMemory CMemory.TensorView CMemory.EncodedTensor FinitePreflight
set_option maxRecDepth 10000

variable [interface : CInterface]

/-- Every product coordinate evaluates to the encoded total product. -/
theorem evaluates (a b : Values shape) (heap : Heap) (left right : Option Address)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b)) :
    FinitePreflight.Evaluates .mul (MultiplicationTotal.result a b) heap left right := by
  intro i
  obtain ⟨leftBase, left_eq, leftRead⟩ := read_left i
  obtain ⟨rightBase, right_eq, rightRead⟩ := read_right i
  simp only [Fin.getElem_fin, finiteBits_get] at leftRead rightRead
  let env := CLoops.counterEnv
    (FinitePreflight.locals (FinitePreflight.parameters left right shape.volume) (MultiplicationTotal.result a b) i.val)
    "k" i.val
  have counter : env "k" = some (.integer i.val) := by simp [env, CLoops.counterEnv, CBody.bind]
  have leftEval := index_eval env heap "left" leftBase i.val
    (by simp [env, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, FinitePreflight.parameters, left_eq]) counter
  have rightEval := index_eval env heap "right" rightBase i.val
    (by simp [env, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, FinitePreflight.parameters, right_eq]) counter
  simp only [Fin.getElem_fin, MultiplicationTotal.result_get]
  exact CArithmetic.eval_mul CBody.legacyExpressions env _ heap (indexed "left") (indexed "right")
    a[i] b[i] (leftEval.trans leftRead) (rightEval.trans rightRead)

theorem function_reaches (a b : Values shape) (heap : Heap) (left right : Option Address)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32)
    (double_type : interface.types "double" = some .float64) :
    Transition.Reaches CLoops.machine.step
      (.running function.body (FinitePreflight.parameters left right shape.volume) FinitePreflight.parameterTypes heap)
      (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)), heap⟩) :=
  operation_reaches _ .mul _ heap left right (evaluates a b heap left right read_left read_right)
    bounded size_type int_type double_type

theorem function_correct (a b : Values shape) (heap : Heap) (left right : Option Address)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32)
    (double_type : interface.types "double" = some .float64) (behavior) :
    CLoops.machine.Behaves
      (.running function.body (FinitePreflight.parameters left right shape.volume) FinitePreflight.parameterTypes heap) behavior ↔
      behavior = .terminates
        ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)), heap⟩ :=
  CLoops.machine.behavior_iff
    (function_reaches a b heap left right read_left read_right bounded size_type int_type double_type) rfl

end Rumoca.CTensor.ProductPreflight
