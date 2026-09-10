import RumocaC.TensorFillCode
import RumocaC.TensorWriter
import RumocaC.LoopCalls
import RumocaC.Algorithm
import RumocaCore.Solve.Tensor.Finite

/-! Exact tensor fills, including signed zero, through the actual counted C
body and ordinary function call. This implements Solve initialization/seed
registers; it performs no source initialization analysis or AD lowering. -/
noncomputable section
namespace Rumoca.CTensor.Fill
open CTree CMemory CMemory.TensorView Solve.Tensor
variable [interface : CInterface]
set_option maxRecDepth 10000

structure HeaderTypes (interface : CInterface) : Prop where
  size : interface.types "size_t" = some .size
  output : interface.types "double *" = some .pointer
  scalar : interface.types "double" = some .float64

def parameters (value : Binary64.Value) (output : Address) (count : Nat) : CBody.Locals := fun name =>
  if name = "value" then some (.finite value)
  else if name = "out" then some (.pointer (some output))
  else if name = "count" then some (.integer count) else none

def parameterTypes : CLoops.Types := fun name =>
  if name = "value" then some .float64
  else if name = "out" then some .pointer
  else if name = "count" then some .size else none

def argumentValues (value : Binary64.Value) (output : Address) (count : Nat) : List Value :=
  [.finite value, .pointer (some output), .integer count]

theorem function_reaches (shape : Tensor.Shape) (value : Binary64.Value) (output : Address) (heap : Heap)
    (writable : Writable heap output shape.volume) (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size) :
    Transition.Reaches CLoops.machine.step
      (.running function.body (parameters value output shape.volume) parameterTypes heap)
      (.returned ⟨.void, written heap output (Tensor.Value.fill shape value) shape.volume⟩) := by
  apply writer_reaches (.id "value") (Tensor.Value.fill shape value) (parameters value output shape.volume)
    parameterTypes heap output (by simp [parameters]) (by simp [parameters]) (by simp [parameters])
    writable bounded size_type
  intro i
  simp [CLoops.eval, CBody.eval, CBody.resolve, CLoops.counterEnv, CBody.bind, parameters]

theorem bind_parameters (value : Binary64.Value) (output : Address) (count : Nat)
    (header : HeaderTypes interface) (bounded : count < 2 ^ 64) :
    CCalls.parameters function.signature.parameters (argumentValues value output count) =
      some (parameters value output count) := by
  have hs := CLoops.Calls.cast_of_type "size_t" .size (.integer count) (.integer count)
    header.size (CLoops.convert_size_nat count bounded)
  have ho := CLoops.Calls.cast_of_type "double *" .pointer (.pointer (some output)) (.pointer (some output))
    header.output rfl
  have hv := CLoops.Calls.cast_of_type "double" .float64 (.finite value) (.finite value) header.scalar rfl
  have countBound := CLoops.Calls.bind_parameter ⟨"size_t", "count", false⟩ []
    (.integer count) (.integer count) [] (fun _ => none) rfl rfl rfl hs
  have outputBound := CLoops.Calls.bind_parameter ⟨"double *", "out", false⟩ _
    (.pointer (some output)) (.pointer (some output)) _ _ rfl countBound (by simp [CBody.bind]) ho
  have valueBound := CLoops.Calls.bind_parameter ⟨"double", "value", false⟩ _
    (.finite value) (.finite value) _ _ rfl outputBound (by simp [CBody.bind]) hv
  have he : CBody.bind (CBody.bind (CBody.bind (fun _ => none) "count" (.integer count))
      "out" (.pointer (some output))) "value" (.finite value) = parameters value output count := by
    funext name; rfl
  simpa only [function, argumentValues, he] using valueBound

theorem bind_types (header : HeaderTypes interface) :
    CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes := by
  have he : CLoops.bindType (CLoops.bindType (CLoops.bindType (fun _ => none) "count" .size)
      "out" .pointer) "value" .float64 = parameterTypes := by funext name; rfl
  simpa only [function, CLoops.Calls.parameterTypes, Bool.false_eq_true, ↓reduceIte,
    bind, Option.bind_some, pure, CLoops.bindType, Option.isSome_none,
    header.size, header.output, header.scalar] using congrArg some he

theorem helper_call_reaches (definitions : CLoops.Calls.Definitions)
    (shape : Tensor.Shape) (value : Binary64.Value) (output : Address) (heap : Heap)
    (stack : CLoops.Calls.Continuation) (found : definitions function.signature.name = some function)
    (header : HeaderTypes interface) (writable : Writable heap output shape.volume)
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling function.signature.name (argumentValues value output shape.volume) heap stack)
      (.returning (written heap output (Tensor.Value.fill shape value) shape.volume) stack) :=
  CLoops.Calls.call_reaches definitions _ _ heap _ function _ _ stack found rfl
    (bind_parameters value output shape.volume header bounded) (bind_types header)
    (function_reaches shape value output heap writable bounded header.size)

theorem helper_call_correct (definitions : CLoops.Calls.Definitions)
    (shape : Tensor.Shape) (value : Binary64.Value) (output : Address) (heap : Heap)
    (found : definitions function.signature.name = some function)
    (header : HeaderTypes interface) (writable : Writable heap output shape.volume)
    (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling function.signature.name (argumentValues value output shape.volume) heap .done) behavior ↔
      behavior = .terminates (written heap output (Tensor.Value.fill shape value) shape.volume) := by
  have ran := helper_call_reaches definitions shape value output heap .done found header writable bounded
  exact (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

theorem invoke_reaches (definitions : CLoops.Calls.Definitions)
    (shape : Tensor.Shape) (value : Binary64.Value) (output : Address) (heap : Heap)
    (argsValue argsOutput argsCount : Expr) (env : CBody.Locals) (types : CLoops.Types)
    (rest : List Stmt) (stack : CLoops.Calls.Continuation)
    (found : definitions function.signature.name = some function)
    (header : HeaderTypes interface) (unshadowed : env function.signature.name = none)
    (hv : CBody.eval env heap argsValue = some (.finite value))
    (ho : CBody.eval env heap argsOutput = some (.pointer (some output)))
    (hc : CBody.eval env heap argsCount = some (.integer shape.volume))
    (writable : Writable heap output shape.volume) (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running (invoke argsValue argsOutput argsCount :: rest) env types heap) stack)
      (.body (.running rest env types
        (written heap output (Tensor.Value.fill shape value) shape.volume)) stack) := by
  have started : CLoops.Calls.next definitions
      (.body (.running (invoke argsValue argsOutput argsCount :: rest) env types heap) stack) =
      some (.calling function.signature.name (argumentValues value output shape.volume) heap
        (.caller rest env types stack)) := by
    simp only [function] at unshadowed
    simp [invoke, function, CLoops.Calls.next, CLoops.next, CLoops.eval, CBody.eval,
      CLoops.Calls.enterCall, CCalls.arguments, hv, ho, hc, argumentValues, unshadowed]
  exact .next started ((helper_call_reaches definitions shape value output heap _ found header
    writable bounded).trans (.next rfl (.refl _)))

theorem literal_eval (literal : Literal) (env : CBody.Locals) (heap : Heap)
    (scalar : interface.types "double" = some .float64) :
    CBody.eval env heap (CAlgorithm.literal literal) =
      some (.finite (literal.eval Binary64.positiveZero Binary64.one)) := by
  cases literal <;> simp [CAlgorithm.literal, CBody.eval, CBody.cast, scalar, convert, Literal.eval]

/-- The returned buffer is the actual Solve fill-program result, for every
entry environment and either literal used by initialization and forward AD. -/
theorem solve_fill_correct (definitions : CLoops.Calls.Definitions)
    (shape : Tensor.Shape) (literal : Literal) (env : Env Binary64.Value Γ) (output : Address) (heap : Heap)
    (found : definitions function.signature.name = some function)
    (header : HeaderTypes interface) (writable : Writable heap output shape.volume)
    (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling function.signature.name
        (argumentValues (literal.eval Binary64.positiveZero Binary64.one) output shape.volume) heap .done) behavior ↔
      behavior = .terminates (written heap output
        ((Solve.Tensor.fill shape literal).eval Finite.ops Binary64.positiveZero Binary64.one env) shape.volume) :=
  helper_call_correct definitions shape _ output heap found header writable bounded behavior

end Rumoca.CTensor.Fill
