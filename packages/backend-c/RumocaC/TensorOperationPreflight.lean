import RumocaC.TensorFinitePreflight
import RumocaC.TensorFiniteScanCalls

/-! The read-only preflight of a shared binary tensor operation, for every
operation whose coordinates evaluate to prepared result encodings. Evaluation
and calls through the canonical contextual machine preserve the entire heap,
require no writable storage or separation, and return the Solve classifier of
the encoded results. Each operation supplies only its coordinate evaluation. -/
noncomputable section
namespace Rumoca.CTensor.FinitePreflight
open CTree CMemory CMemory.EncodedTensor
set_option maxRecDepth 10000

def parameters (left right : Option Address) (count : Nat) : CBody.Locals := fun name =>
  if name = "left" then some (.pointer left)
  else if name = "right" then some (.pointer right)
  else if name = "count" then some (.integer count) else none

def parameterTypes : CLoops.Types := fun name =>
  if name = "left" then some .pointer
  else if name = "right" then some .pointer
  else if name = "count" then some .size else none

structure HeaderTypes (interface : CInterface) : Prop extends FiniteScan.HeaderTypes interface where
  scalar : interface.types "double" = some .float64

def argumentValues (left right : Option Address) (count : Nat) : List Value :=
  [.pointer left, .pointer right, .integer count]

variable [interface : CInterface]

/-- Every visited coordinate of the operation evaluates to its prepared result
encoding in the preflight's own loop environment. -/
def Evaluates (op : BinOp) (values : Bits shape) (heap : Heap) (left right : Option Address) : Prop :=
  ∀ i : Fin shape.volume,
    CLoops.eval (CLoops.counterEnv (locals (parameters left right shape.volume) values i.val) "k" i.val)
      (localTypes parameterTypes) heap (coordinate op) = some (.float64 values[i])

theorem operation_reaches (name : String) (op : BinOp) (values : Bits shape) (heap : Heap)
    (left right : Option Address) (evaluated : Evaluates op values heap left right)
    (bounded : shape.volume < 2 ^ 64)
    (size_type : interface.types "size_t" = some .size)
    (int_type : interface.types "int32_t" = some .int32)
    (double_type : interface.types "double" = some .float64) :
    Transition.Reaches CLoops.machine.step
      (.running (operation name op).body (parameters left right shape.volume) parameterTypes heap)
      (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩) :=
  body_reaches (coordinate op) values (parameters left right shape.volume) parameterTypes heap
    (by simp [parameters]) (by simp [parameters]) (by simp [parameters]) (by simp [parameters])
    bounded size_type int_type double_type evaluated

theorem bind_parameters (name : String) (op : BinOp) (left right : Option Address) (count : Nat)
    (header : HeaderTypes interface) (bounded : count < 2 ^ 64) :
    CCalls.parameters (operation name op).signature.parameters (argumentValues left right count) =
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

theorem bind_types (name : String) (op : BinOp) (header : HeaderTypes interface) :
    CLoops.Calls.parameterTypes (operation name op).signature.parameters = some parameterTypes := by
  have same : CLoops.bindType (CLoops.bindType (CLoops.bindType (fun _ => none)
      "count" .size) "right" .pointer) "left" .pointer = parameterTypes := by funext name; rfl
  simpa only [operation, CLoops.Calls.parameterTypes, CCalls.parameterType,
    Bool.false_eq_true, ↓reduceIte, bind, Option.bind_some, pure, CLoops.bindType,
    Option.isSome_none, header.size, header.input] using congrArg some same

omit interface in
theorem body_field_free (name : String) (op : BinOp) :
    CDeclaredMembers.FieldFree.AdmittedBody (operation name op).body := by
  simp [CDeclaredMembers.FieldFree.AdmittedBody, CDeclaredMembers.FieldFree.body,
    CDeclaredMembers.FieldFree.expressions, CDeclaredMembers.FieldFree.sites,
    CDeclaredMembers.FieldFree.expression, CDeclaredMembers.FieldFree.argumentList,
    operation, coordinate, body, segment, segmentWith,
    iteration, FiniteScan.iterationFor, Expr.nonfinite, indexed,
    CLoops.counted, CLoops.loop, CLoops.counterStep]

theorem call_reaches (name : String) (op : BinOp) (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (values : Bits shape) (heap : Heap) (left right : Option Address)
    (stack : CCalls.Typed.Continuation)
    (found : p.definitions name = some (.tree (operation name op)))
    (header : HeaderTypes interface) (evaluated : Evaluates op values heap left right)
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CContextMachine.machine (CContextMachine.declared declarations objects) p).step
      (.calling name (argumentValues left right shape.volume) heap stack)
      (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values)) heap stack) := by
  have entered : CContextMachine.next (CContextMachine.declared declarations objects) p
      (.calling name (argumentValues left right shape.volume) heap stack) =
      some (.body (.running (operation name op).body (parameters left right shape.volume)
        parameterTypes heap) "int32_t" stack) := by
    simp only [CContextMachine.next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions,
      found, bind_parameters name op left right shape.volume header bounded,
      bind_types name op header, bind, Option.bind_some, pure]
    rfl
  have ran := CContextMachine.FieldFree.body_reaches_context declarations objects p
    (operation_reaches name op values heap left right evaluated bounded header.size header.result
      header.scalar)
    "int32_t" stack (body_field_free name op)
  have returned : CContextMachine.next (CContextMachine.declared declarations objects) p
      (.body (.returned ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩)
        "int32_t" stack) =
      some (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values)) heap stack) := by
    simp [CContextMachine.next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions,
      FiniteScan.return_cast header.toHeaderTypes]
  exact .next entered (ran.trans (.next returned (.refl _)))

theorem call_correct (name : String) (op : BinOp) (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (values : Bits shape) (heap : Heap) (left right : Option Address)
    (found : p.definitions name = some (.tree (operation name op)))
    (header : HeaderTypes interface) (evaluated : Evaluates op values heap left right)
    (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CContextMachine.machine (CContextMachine.declared declarations objects) p).Behaves
      (.calling name (argumentValues left right shape.volume) heap .done) behavior ↔
      behavior = .terminates
        ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩ := by
  have ran := call_reaches name op declarations objects p values heap left right .done found header
    evaluated bounded
  exact (CContextMachine.machine (CContextMachine.declared declarations objects) p).behavior_iff
    (ran.trans (.next rfl (.refl _))) rfl

end Rumoca.CTensor.FinitePreflight
