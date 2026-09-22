import RumocaC.TensorFiniteScan
import RumocaC.FieldFreeLoop

/-! Value-returning scanner calls through the canonical contextual C machine.
The actual helper body executes, the return value is converted using its header
type, and arbitrary callers/declared-object contexts retain the same heap. -/
noncomputable section
namespace Rumoca.CTensor.FiniteScan
open CTree CMemory CMemory.EncodedTensor
set_option maxRecDepth 10000

structure HeaderTypes (interface : CInterface) : Prop where
  size : interface.types "size_t" = some .size
  input : interface.types "const double *" = some .pointer
  result : interface.types "int32_t" = some .int32

def argumentValues (input : Option Address) (count : Nat) : List Value :=
  [.pointer input, .integer count]

variable [interface : CInterface]

theorem bind_parameters (input : Option Address) (count : Nat)
    (header : HeaderTypes interface) (bounded : count < 2 ^ 64) :
    CCalls.parameters function.signature.parameters (argumentValues input count) =
      some (parameters input count) := by
  have sizeCast := CLoops.Calls.cast_of_type "size_t" .size (.integer count) (.integer count)
    header.size (CLoops.convert_size_nat count bounded)
  have pointerCast := CLoops.Calls.cast_of_type "const double *" .pointer (.pointer input) (.pointer input)
    header.input rfl
  have countBound := CLoops.Calls.bind_parameter ⟨"size_t", "count", false⟩ []
    (.integer count) (.integer count) [] (fun _ => none) rfl rfl rfl sizeCast
  have inputBound := CLoops.Calls.bind_parameter ⟨"const double *", "values", false⟩ _
    (.pointer input) (.pointer input) _ _ rfl countBound (by simp [CBody.bind]) pointerCast
  exact inputBound

theorem bind_types (header : HeaderTypes interface) :
    CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes := by
  have same : CLoops.bindType (CLoops.bindType (fun _ => none) "count" .size)
      "values" .pointer = parameterTypes := by funext name; rfl
  simpa only [function, CLoops.Calls.parameterTypes, CCalls.parameterType,
    Bool.false_eq_true, ↓reduceIte, bind, Option.bind_some, pure, CLoops.bindType,
    Option.isSome_none, header.size, header.input] using congrArg some same

theorem return_cast (header : HeaderTypes interface) (finite : Bool) :
    CCalls.returnCast "int32_t" (CBody.boolean finite) = some (CBody.boolean finite) := by
  cases finite <;> simp [CCalls.returnCast, CBody.cast, header.result, CBody.boolean, convert]

omit interface in
theorem body_field_free : CDeclaredMembers.FieldFree.AdmittedBody function.body := by
  simp [CDeclaredMembers.FieldFree.AdmittedBody, CDeclaredMembers.FieldFree.body,
    CDeclaredMembers.FieldFree.expressions, CDeclaredMembers.FieldFree.sites,
    CDeclaredMembers.FieldFree.expression, CDeclaredMembers.FieldFree.argumentList,
    function, iteration, indexed, CLoops.counted, CLoops.loop, CLoops.counterStep]

theorem call_reaches (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (input : Option Address) (values : Bits shape) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : HeaderTypes interface) (readable : Readable heap input values)
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CContextMachine.machine (CContextMachine.declared declarations objects) p).step
      (.calling function.signature.name (argumentValues input shape.volume) heap stack)
      (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values)) heap stack) := by
  have entered : CContextMachine.next (CContextMachine.declared declarations objects) p
      (.calling function.signature.name (argumentValues input shape.volume) heap stack) =
      some (.body (.running function.body (parameters input shape.volume) parameterTypes heap)
        "int32_t" stack) := by
    simp only [CContextMachine.next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions,
      found, bind_parameters input shape.volume header bounded, bind_types header,
      bind, Option.bind_some, pure]
    rfl
  have ran := CContextMachine.FieldFree.body_reaches_context declarations objects p
    (function_reaches input values heap readable bounded header.size header.result) "int32_t" stack
    body_field_free
  have returned : CContextMachine.next (CContextMachine.declared declarations objects) p
      (.body (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩) "int32_t" stack) =
      some (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values)) heap stack) := by
    simp [CContextMachine.next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, return_cast header]
  exact .next entered (ran.trans (.next returned (.refl _)))

theorem call_correct (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (input : Option Address) (values : Bits shape) (heap : Heap)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : HeaderTypes interface) (readable : Readable heap input values)
    (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CContextMachine.machine (CContextMachine.declared declarations objects) p).Behaves
      (.calling function.signature.name (argumentValues input shape.volume) heap .done) behavior ↔
      behavior = .terminates ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩ := by
  have ran := call_reaches declarations objects p input values heap .done found header readable bounded
  exact (CContextMachine.machine (CContextMachine.declared declarations objects) p).behavior_iff
    (ran.trans (.next rfl (.refl _))) rfl

end Rumoca.CTensor.FiniteScan
