import RumocaC.TensorProductPreflight
import RumocaC.TensorFiniteScanCalls

/-! Actual preflight calls in the canonical C machine. The unchanged heap is
preserved across arbitrary saved callers and declared-object contexts. -/
noncomputable section
namespace Rumoca.CTensor.ProductPreflight
open CTree CMemory CMemory.TensorView CMemory.EncodedTensor
set_option maxRecDepth 10000

structure HeaderTypes (interface : CInterface) : Prop extends FiniteScan.HeaderTypes interface where
  scalar : interface.types "double" = some .float64

def argumentValues (left right : Option Address) (count : Nat) : List Value :=
  [.pointer left, .pointer right, .integer count]

variable [interface : CInterface]

theorem bind_parameters (left right : Option Address) (count : Nat)
    (header : HeaderTypes interface) (bounded : count < 2 ^ 64) :
    CCalls.parameters function.signature.parameters (argumentValues left right count) =
      some (parameters left right count) := by
  have sizeCast := CLoops.Calls.cast_of_type "size_t" .size (.integer count) (.integer count)
    header.size (CLoops.convert_size_nat count bounded)
  have pointerCast (input : Option Address) :=
    CLoops.Calls.cast_of_type "const double *" .pointer (.pointer input) (.pointer input)
      header.input rfl
  have countBound := CLoops.Calls.bind_parameter ⟨"size_t", "count", false⟩ []
    (.integer count) (.integer count) [] (fun _ => none) rfl rfl rfl sizeCast
  have rightBound := CLoops.Calls.bind_parameter ⟨"const double *", "right", false⟩ _
    (.pointer right) (.pointer right) _ _ rfl countBound (by simp [CBody.bind]) (pointerCast right)
  have leftBound := CLoops.Calls.bind_parameter ⟨"const double *", "left", false⟩ _
    (.pointer left) (.pointer left) _ _ rfl rightBound (by simp [CBody.bind]) (pointerCast left)
  exact leftBound

theorem bind_types (header : HeaderTypes interface) :
    CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes := by
  have same : CLoops.bindType (CLoops.bindType (CLoops.bindType (fun _ => none)
      "count" .size) "right" .pointer) "left" .pointer = parameterTypes := by funext name; rfl
  simpa only [function, CLoops.Calls.parameterTypes, CCalls.parameterType,
    Bool.false_eq_true, ↓reduceIte, bind, Option.bind_some, pure, CLoops.bindType,
    Option.isSome_none, header.size, header.input] using congrArg some same

omit interface in
theorem body_field_free : CDeclaredMembers.FieldFree.AdmittedBody function.body := by
  simp [CDeclaredMembers.FieldFree.AdmittedBody, CDeclaredMembers.FieldFree.body,
    CDeclaredMembers.FieldFree.expressions, CDeclaredMembers.FieldFree.sites,
    CDeclaredMembers.FieldFree.expression, CDeclaredMembers.FieldFree.argumentList,
    function, value, FinitePreflight.body, FinitePreflight.iteration, FiniteScan.iterationFor, indexed,
    CLoops.counted, CLoops.loop, CLoops.counterStep]

theorem call_reaches (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (a b : Values shape) (heap : Heap) (left right : Option Address) (stack : CCalls.Typed.Continuation)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : HeaderTypes interface)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CContextMachine.machine (CContextMachine.declared declarations objects) p).step
      (.calling function.signature.name (argumentValues left right shape.volume) heap stack)
      (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)))
        heap stack) := by
  have entered : CContextMachine.next (CContextMachine.declared declarations objects) p
      (.calling function.signature.name (argumentValues left right shape.volume) heap stack) =
      some (.body (.running function.body (parameters left right shape.volume) parameterTypes heap)
        "int32_t" stack) := by
    simp only [CContextMachine.next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions,
      found, bind_parameters left right shape.volume header bounded, bind_types header,
      bind, Option.bind_some, pure]
    rfl
  have ran := CContextMachine.FieldFree.body_reaches_context declarations objects p
    (function_reaches a b heap left right read_left read_right bounded header.size header.result header.scalar)
    "int32_t" stack body_field_free
  have returned : CContextMachine.next (CContextMachine.declared declarations objects) p
      (.body (.returned
        ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)), heap⟩)
        "int32_t" stack) =
      some (.returning
        (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b))) heap stack) := by
    simp [CContextMachine.next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions,
      FiniteScan.return_cast header.toHeaderTypes]
  exact .next entered (ran.trans (.next returned (.refl _)))

theorem call_correct (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (a b : Values shape) (heap : Heap) (left right : Option Address)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : HeaderTypes interface)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CContextMachine.machine (CContextMachine.declared declarations objects) p).Behaves
      (.calling function.signature.name (argumentValues left right shape.volume) heap .done) behavior ↔
      behavior = .terminates
        ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)), heap⟩ := by
  have ran := call_reaches declarations objects p a b heap left right .done found header
    read_left read_right bounded
  exact (CContextMachine.machine (CContextMachine.declared declarations objects) p).behavior_iff
    (ran.trans (.next rfl (.refl _))) rfl

end Rumoca.CTensor.ProductPreflight
