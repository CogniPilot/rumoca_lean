import RumocaC.TensorProofs
import RumocaC.LoopCalls

/-! Bind and call the actual tensor helper functions. The proofs cover the
declared parameter types, fresh local scope, body execution and caller
restoration. The header dictionary is explicit; this is not a native ABI
or allocation theorem. -/
noncomputable section
namespace Rumoca.CTensor
open CTree CMemory CMemory.TensorView Solve.Tensor
variable [interface : CInterface]
set_option maxRecDepth 10000

structure HeaderTypes (interface : CInterface) : Prop where
  size : interface.types "size_t" = some .size
  input : interface.types "const double *" = some .pointer
  output : interface.types "double *" = some .pointer

def argumentValues (left right output : Address) (count : Nat) : List Value :=
  [.pointer (some left), .pointer (some right), .pointer (some output), .integer count]

theorem bind_parameters (op : Tensor.BinaryOp) (left right output : Address) (count : Nat)
    (header : HeaderTypes interface) (bounded : count < 2 ^ 64) :
    CCalls.parameters (function op).signature.parameters (argumentValues left right output count) =
      some (parameters left right output count) := by
  have hs := CLoops.Calls.cast_of_type "size_t" .size (.integer count) (.integer count)
    header.size (CLoops.convert_size_nat count bounded)
  have hi (p : Address) : CBody.cast "const double *" (.pointer (some p)) = some (.pointer (some p)) := by
    simp [CBody.cast, header.input, convert]
  have ho (p : Address) : CBody.cast "double *" (.pointer (some p)) = some (.pointer (some p)) := by
    simp [CBody.cast, header.output, convert]
  have countBound := CLoops.Calls.bind_parameter ⟨"size_t", "count", false⟩ []
    (.integer count) (.integer count) [] (fun _ => none) rfl rfl rfl hs
  have outputBound := CLoops.Calls.bind_parameter ⟨"double *", "out", false⟩ _
    (.pointer (some output)) (.pointer (some output)) _ _ rfl countBound
    (by simp [CBody.bind]) (ho output)
  have rightBound := CLoops.Calls.bind_parameter ⟨"const double *", "right", false⟩ _
    (.pointer (some right)) (.pointer (some right)) _ _ rfl outputBound
    (by simp [CBody.bind]) (hi right)
  have leftBound := CLoops.Calls.bind_parameter ⟨"const double *", "left", false⟩ _
    (.pointer (some left)) (.pointer (some left)) _ _ rfl rightBound
    (by simp [CBody.bind]) (hi left)
  have he : CBody.bind (CBody.bind (CBody.bind (CBody.bind (fun _ => none)
      "count" (.integer count)) "out" (.pointer (some output))) "right" (.pointer (some right)))
      "left" (.pointer (some left)) = parameters left right output count := by
    funext name
    rfl
  cases op <;> simpa only [function, argumentValues, he] using leftBound

theorem bind_types (op : Tensor.BinaryOp) (header : HeaderTypes interface) :
    CLoops.Calls.parameterTypes (function op).signature.parameters = some parameterTypes := by
  have he : (CLoops.bindType
      (CLoops.bindType (CLoops.bindType (CLoops.bindType (fun _ => none) "count" .size)
        "out" .pointer) "right" .pointer) "left" .pointer) = parameterTypes := by
    funext name
    by_cases hl : name = "left" <;> by_cases hr : name = "right" <;>
      by_cases ho : name = "out" <;> by_cases hc : name = "count" <;>
      simp_all [CLoops.bindType, parameterTypes]
  cases op <;>
    simpa only [function, CLoops.Calls.parameterTypes, CCalls.parameterType, Bool.false_eq_true, ↓reduceIte,
      bind, Option.bind_some, pure, CLoops.bindType, Option.isSome_none,
      header.size, header.input, header.output] using congrArg some he

theorem helper_call_reaches (definitions : CLoops.Calls.Definitions) (op : Tensor.BinaryOp)
    (a b : Values shape) (heap : Heap) (left right output : Address)
    (stack : CLoops.Calls.Continuation)
    (found : definitions (function op).signature.name = some (function op))
    (header : HeaderTypes interface)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (domain : ∀ i : Fin shape.volume, Finite.Domain op a[i] b[i]) (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (function op).signature.name (argumentValues left right output shape.volume) heap stack)
      (.returning (written heap output (op.eval Finite.ops a b) shape.volume) stack) := by
  have executed := function_reaches op a b heap left right output read_left read_right write_output
    separate_left separate_right domain bounded header.size
  exact CLoops.Calls.call_reaches definitions _ _ heap _ (function op) _ _ stack found rfl
    (bind_parameters op left right output shape.volume header bounded) (bind_types op header) executed

/-- A complete ordinary call has exactly the independently specified finite
Solve result; parameter binding and return are included in its execution. -/
theorem helper_call_correct (definitions : CLoops.Calls.Definitions) (op : Tensor.BinaryOp)
    (a b result : Values shape) (heap : Heap) (left right output : Address)
    (found : definitions (function op).signature.name = some (function op))
    (header : HeaderTypes interface)
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (finite : Finite.Pointwise op a b result) (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling (function op).signature.name (argumentValues left right output shape.volume) heap .done)
      behavior ↔ behavior = .terminates (written heap output result shape.volume) := by
  obtain ⟨domain, rfl⟩ := (Finite.pointwise_iff _ _ _ _).mp finite
  have ran := helper_call_reaches definitions op a b heap left right output .done found header
    read_left read_right write_output separate_left separate_right domain bounded
  exact (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

theorem invoke_step (definitions : CLoops.Calls.Definitions) (op : Tensor.BinaryOp)
    (argsLeft argsRight argsOutput argsCount : Expr) (left right output : Address) (count : Nat)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (rest : List Stmt)
    (stack : CLoops.Calls.Continuation)
    (unshadowed : env (function op).signature.name = none)
    (hl : CBody.eval env heap argsLeft = some (.pointer (some left)))
    (hr : CBody.eval env heap argsRight = some (.pointer (some right)))
    (ho : CBody.eval env heap argsOutput = some (.pointer (some output)))
    (hc : CBody.eval env heap argsCount = some (.integer count)) :
    CLoops.Calls.next definitions
      (.body (.running (invoke op argsLeft argsRight argsOutput argsCount :: rest) env types heap) stack) =
      some (.calling (function op).signature.name (argumentValues left right output count) heap
        (.caller rest env types stack)) := by
  cases op <;>
    simp [invoke, function, CLoops.Calls.next, CLoops.next, CLoops.eval, CBody.eval,
      CLoops.Calls.enterCall, CCalls.arguments, hl, hr, ho, hc, argumentValues] <;>
    simpa only [function] using unshadowed

theorem invoke_reaches (definitions : CLoops.Calls.Definitions) (op : Tensor.BinaryOp)
    (a b : Values shape) (heap : Heap) (left right output : Address)
    (argsLeft argsRight argsOutput argsCount : Expr) (env : CBody.Locals) (types : CLoops.Types)
    (rest : List Stmt) (stack : CLoops.Calls.Continuation)
    (found : definitions (function op).signature.name = some (function op))
    (header : HeaderTypes interface) (unshadowed : env (function op).signature.name = none)
    (hl : CBody.eval env heap argsLeft = some (.pointer (some left)))
    (hr : CBody.eval env heap argsRight = some (.pointer (some right)))
    (ho : CBody.eval env heap argsOutput = some (.pointer (some output)))
    (hc : CBody.eval env heap argsCount = some (.integer shape.volume))
    (read_left : Reads heap left a) (read_right : Reads heap right b)
    (write_output : Writable heap output shape.volume)
    (separate_left : Separate output left shape.volume) (separate_right : Separate output right shape.volume)
    (domain : ∀ i : Fin shape.volume, Finite.Domain op a[i] b[i]) (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running (invoke op argsLeft argsRight argsOutput argsCount :: rest) env types heap) stack)
      (.body (.running rest env types (written heap output (op.eval Finite.ops a b) shape.volume)) stack) := by
  refine .next (invoke_step definitions op argsLeft argsRight argsOutput argsCount left right output
    shape.volume env types heap rest stack unshadowed hl hr ho hc) ?_
  exact (helper_call_reaches definitions op a b heap left right output _ found header read_left read_right
    write_output separate_left separate_right domain bounded).trans (.next rfl (.refl _))

end Rumoca.CTensor
