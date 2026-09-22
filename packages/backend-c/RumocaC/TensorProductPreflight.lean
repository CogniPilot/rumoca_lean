import RumocaC.TensorProductPreflightCode
import RumocaC.TensorFinitePreflight
import RumocaC.TensorMultiplicationTotal

/-! A preflight of prepared tensor multiplication, including finite-input
overflow, underflow and signed zero. Its result is the Solve classifier of the
same encoded result produced by the existing multiplication helper. Evaluation
preserves the entire heap, requires no writable storage or separation, and
allows null inputs exactly when no coordinate is visited. -/
noncomputable section
namespace Rumoca.CTensor.ProductPreflight
open CTree CMemory CMemory.TensorView CMemory.EncodedTensor
set_option maxRecDepth 10000

def parameters (left right : Option Address) (count : Nat) : CBody.Locals := fun name =>
  if name = "left" then some (.pointer left)
  else if name = "right" then some (.pointer right)
  else if name = "count" then some (.integer count) else none

def parameterTypes : CLoops.Types := fun name =>
  if name = "left" then some .pointer
  else if name = "right" then some .pointer
  else if name = "count" then some .size else none

variable [interface : CInterface]

theorem function_reaches (a b : Values shape) (heap : Heap) (left right : Option Address)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32)
    (double_type : interface.types "double" = some .float64) :
    Transition.Reaches CLoops.machine.step
      (.running function.body (parameters left right shape.volume) parameterTypes heap)
      (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)), heap⟩) := by
  apply FinitePreflight.body_reaches value (MultiplicationTotal.result a b)
    (parameters left right shape.volume) parameterTypes heap
    (by simp [parameters]) (by simp [parameters]) (by simp [parameters]) (by simp [parameters])
    bounded size_type int_type double_type
  intro i
  obtain ⟨leftBase, left_eq, leftRead⟩ := read_left i
  obtain ⟨rightBase, right_eq, rightRead⟩ := read_right i
  simp only [Fin.getElem_fin, finiteBits_get] at leftRead rightRead
  let env := CLoops.counterEnv
    (FinitePreflight.locals (parameters left right shape.volume) (MultiplicationTotal.result a b) i.val)
    "k" i.val
  have counter : env "k" = some (.integer i.val) := by simp [env, CLoops.counterEnv, CBody.bind]
  have leftEval := index_eval env heap "left" leftBase i.val
    (by simp [env, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, parameters, left_eq]) counter
  have rightEval := index_eval env heap "right" rightBase i.val
    (by simp [env, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, parameters, right_eq]) counter
  simp only [Fin.getElem_fin, MultiplicationTotal.result_get]
  exact CArithmetic.eval_mul CBody.legacyExpressions env _ heap (indexed "left") (indexed "right")
    a[i] b[i] (leftEval.trans leftRead) (rightEval.trans rightRead)

theorem function_correct (a b : Values shape) (heap : Heap) (left right : Option Address)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32)
    (double_type : interface.types "double" = some .float64) (behavior) :
    CLoops.machine.Behaves
      (.running function.body (parameters left right shape.volume) parameterTypes heap) behavior ↔
      behavior = .terminates
        ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)), heap⟩ :=
  CLoops.machine.behavior_iff
    (function_reaches a b heap left right read_left read_right bounded size_type int_type double_type) rfl

end Rumoca.CTensor.ProductPreflight
