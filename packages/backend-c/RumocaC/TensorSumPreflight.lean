import RumocaC.TensorSumPreflightCode
import RumocaC.TensorOperationPreflight
import RumocaC.AdditionResults
import RumocaC.TensorWriter
import RumocaCore.Solve.Tensor.Numerical

/-! A preflight of prepared tensor addition on finite inputs, including
overflow to either infinity. Its result is the Solve classifier of the encoded
total sums. Calls preserve the entire heap, require no writable storage or
separation, and allow both inputs to alias. -/
noncomputable section
namespace Rumoca.CTensor.SumPreflight
open CTree CMemory CMemory.TensorView CMemory.EncodedTensor FinitePreflight
set_option maxRecDepth 10000

/-- The encoded total sums of two finite tensors. -/
def result (a b : Values shape) : Bits shape :=
  Solve.Tensor.Numerical.encode (Solve.Tensor.Numerical.add a b)

theorem result_get (a b : Values shape) (i : Nat) (hi : i < shape.volume) :
    (result a b)[i] = (Binary64.addResult a[i] b[i]).encode := by
  simp only [result, Solve.Tensor.Numerical.encode, Solve.Tensor.Numerical.add,
    Tensor.Value.getElem_mapWith, Tensor.Value.getElem_zipWith]

/-- Detection succeeds exactly on the independent finite sum domain. -/
theorem result_allFinite (a b : Values shape) :
    Solve.Tensor.Numerical.allFiniteBits (result a b) = true ↔
      ∀ i : Fin shape.volume,
        -Binary64.overflowUnits < Binary64.units a[i] + Binary64.units b[i] ∧
          Binary64.units a[i] + Binary64.units b[i] < Binary64.overflowUnits := by
  rw [result, Solve.Tensor.Numerical.allFiniteBits_encode, Solve.Tensor.Numerical.add_allFinite_iff]

/-- A failed sum check has a real witness at a coordinate. -/
theorem result_overflow (a b : Values shape) :
    Solve.Tensor.Numerical.allFiniteBits (result a b) = false ↔
      ∃ i : Fin shape.volume,
        Binary64.value a[i] + Binary64.value b[i] ≤ -Binary64.overflowValue ∨
          Binary64.overflowValue ≤ Binary64.value a[i] + Binary64.value b[i] := by
  rw [result, Solve.Tensor.Numerical.add_detects_iff]
  apply exists_congr
  intro i
  rw [← Binary64.sum_above_negative_overflow, ← Binary64.sum_below_overflow]
  constructor
  · intro outside
    by_contra inside
    push Not at inside
    exact outside inside
  · rintro (low | high) ⟨lower, upper⟩
    · exact absurd low (not_le_of_gt lower)
    · exact absurd high (not_le_of_gt upper)

variable [interface : CInterface]

/-- Every sum coordinate evaluates to the encoded total sum. -/
theorem evaluates (a b : Values shape) (heap : Heap) (left right : Option Address)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b)) :
    FinitePreflight.Evaluates .add (result a b) heap left right := by
  intro i
  obtain ⟨leftBase, left_eq, leftRead⟩ := read_left i
  obtain ⟨rightBase, right_eq, rightRead⟩ := read_right i
  simp only [Fin.getElem_fin, finiteBits_get] at leftRead rightRead
  let env := CLoops.counterEnv
    (FinitePreflight.locals (FinitePreflight.parameters left right shape.volume) (result a b) i.val) "k" i.val
  have counter : env "k" = some (.integer i.val) := by simp [env, CLoops.counterEnv, CBody.bind]
  have leftEval := index_eval env heap "left" leftBase i.val
    (by simp [env, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, FinitePreflight.parameters, left_eq]) counter
  have rightEval := index_eval env heap "right" rightBase i.val
    (by simp [env, CLoops.counterEnv, FinitePreflight.locals, CBody.bind, FinitePreflight.parameters, right_eq]) counter
  simp only [Fin.getElem_fin, result_get]
  exact CArithmetic.eval_index_add CBody.legacyExpressions env _ heap (.id "left") (.id "k")
    (indexed "right") a[i] b[i] (leftEval.trans leftRead) (rightEval.trans rightRead)

theorem call_reaches (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (a b : Values shape) (heap : Heap) (left right : Option Address) (stack : CCalls.Typed.Continuation)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : FinitePreflight.HeaderTypes interface)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CContextMachine.machine (CContextMachine.declared declarations objects) p).step
      (.calling function.signature.name (FinitePreflight.argumentValues left right shape.volume) heap stack)
      (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (result a b))) heap stack) :=
  FinitePreflight.call_reaches _ .add declarations objects p _ heap left right stack found header
    (evaluates a b heap left right read_left read_right) bounded

theorem call_correct (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (a b : Values shape) (heap : Heap) (left right : Option Address)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : FinitePreflight.HeaderTypes interface)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CContextMachine.machine (CContextMachine.declared declarations objects) p).Behaves
      (.calling function.signature.name (FinitePreflight.argumentValues left right shape.volume) heap .done) behavior ↔
      behavior = .terminates ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (result a b)), heap⟩ :=
  FinitePreflight.call_correct _ .add declarations objects p _ heap left right found header
    (evaluates a b heap left right read_left read_right) bounded behavior

end Rumoca.CTensor.SumPreflight
