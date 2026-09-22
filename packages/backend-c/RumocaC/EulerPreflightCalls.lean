import RumocaC.EulerPreflight
import RumocaC.FieldFreeLoop

/-! Contextual calls for the fixed-rate scalar preflight. Parameter
and return conversions use explicit header types. This proves the modeled C
call boundary, not a native ABI, public clock policy or actual-file contract. -/
noncomputable section
namespace Rumoca.CEulerPreflight
open CTree CMemory
set_option maxRecDepth 10000

structure HeaderTypes (interface : CInterface) : Prop where
  scalar : interface.types "double" = some .float64
  size : interface.types "size_t" = some .size
  result : interface.types "int32_t" = some .int32

def argumentValues (initial rate : Binary64.Value) (count : Nat) : List Value :=
  [.finite initial, .finite rate, .integer count]

variable [interface : CInterface]

theorem bind_parameters (initial rate : Binary64.Value) (count : Nat)
    (header : HeaderTypes interface) (bounded : count < 2 ^ 64) :
    CCalls.parameters function.signature.parameters (argumentValues initial rate count) =
      some (parameters initial rate count) := by
  have sizeCast := CLoops.Calls.cast_of_type "size_t" .size (.integer count) (.integer count)
    header.size (CLoops.convert_size_nat count bounded)
  have scalarCast (value : Binary64.Value) :=
    CLoops.Calls.cast_of_type "double" .float64 (.finite value) (.finite value)
      header.scalar rfl
  have countBound := CLoops.Calls.bind_parameter ⟨"size_t", "count", false⟩ []
    (.integer count) (.integer count) [] (fun _ => none) rfl rfl rfl sizeCast
  have rateBound := CLoops.Calls.bind_parameter ⟨"double", "rate", false⟩ _
    (.finite rate) (.finite rate) _ _ rfl countBound (by simp [CBody.bind]) (scalarCast rate)
  have initialBound := CLoops.Calls.bind_parameter ⟨"double", "initial", false⟩ _
    (.finite initial) (.finite initial) _ _ rfl rateBound (by simp [CBody.bind]) (scalarCast initial)
  exact initialBound

theorem bind_types (header : HeaderTypes interface) :
    CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes := by
  have same : CLoops.bindType (CLoops.bindType (CLoops.bindType (fun _ => none)
      "count" .size) "rate" .float64) "initial" .float64 = parameterTypes := by
    funext name; rfl
  simpa only [function, CLoops.Calls.parameterTypes, CCalls.parameterType,
    Bool.false_eq_true, ↓reduceIte, bind, Option.bind_some, pure, CLoops.bindType,
    Option.isSome_none, header.size, header.scalar] using congrArg some same

private theorem return_cast (header : HeaderTypes interface) (valid : Bool) :
    CCalls.returnCast "int32_t" (CBody.boolean valid) = some (CBody.boolean valid) := by
  cases valid <;> simp [CCalls.returnCast, CBody.cast, header.result, CBody.boolean, convert]

omit interface in
theorem body_field_free : CDeclaredMembers.FieldFree.AdmittedBody function.body := by
  simp [CDeclaredMembers.FieldFree.AdmittedBody, CDeclaredMembers.FieldFree.body,
    CDeclaredMembers.FieldFree.expressions, CDeclaredMembers.FieldFree.sites,
    CDeclaredMembers.FieldFree.expression, CDeclaredMembers.FieldFree.argumentList,
    function, segment, iteration, active, copySample, guard, CTensor.FiniteScan.iterationFor,
    CLoops.counted, CLoops.loop, CLoops.counterStep]

/-- Stop at return to the saved caller; no claim about what that caller does
afterward. Every declared-object context and saved continuation is allowed. -/
theorem call_reaches (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (initial rate : Binary64.Value) (count : Nat) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : HeaderTypes interface) (bounded : count < 2 ^ 64) :
    Transition.Reaches (CContextMachine.machine (CContextMachine.declared declarations objects) p).step
      (.calling function.signature.name (argumentValues initial rate count) heap stack)
      (.returning (CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome) heap stack) := by
  have entered : CContextMachine.next (CContextMachine.declared declarations objects) p
      (.calling function.signature.name (argumentValues initial rate count) heap stack) =
      some (.body (.running function.body (parameters initial rate count) parameterTypes heap)
        "int32_t" stack) := by
    simp only [CContextMachine.next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions,
      found, bind_parameters initial rate count header bounded, bind_types header,
      bind, Option.bind_some, pure]
    rfl
  obtain ⟨segmentRan, flag, _⟩ := segment_reaches initial rate count heap
    [.ret (some (.id "valid"))] bounded header.size header.result header.scalar
  have bodyReturn : CLoops.next
      (.running [.ret (some (.id "valid"))] (finalLocals initial rate count) localTypes heap) =
      some (.returned ⟨CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome, heap⟩) := by
    simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
      CBody.eval, CBody.evalWith, CBody.resolve, flag]
  have ran := CContextMachine.FieldFree.body_reaches_context declarations objects p
    (segmentRan.trans (.next bodyReturn (.refl _))) "int32_t" stack body_field_free
  have returned : CContextMachine.next (CContextMachine.declared declarations objects) p
      (.body (.returned ⟨CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome, heap⟩)
        "int32_t" stack) =
      some (.returning (CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome) heap stack) := by
    simp [CContextMachine.next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, return_cast header]
  exact .next entered (ran.trans (.next returned (.refl _)))

theorem call_correct (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (initial rate : Binary64.Value) (count : Nat) (heap : Heap)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : HeaderTypes interface) (bounded : count < 2 ^ 64) (behavior) :
    (CContextMachine.machine (CContextMachine.declared declarations objects) p).Behaves
      (.calling function.signature.name (argumentValues initial rate count) heap .done) behavior ↔
      behavior = .terminates ⟨CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome, heap⟩ := by
  have ran := call_reaches declarations objects p initial rate count heap .done found header bounded
  exact (CContextMachine.machine (CContextMachine.declared declarations objects) p).behavior_iff
    (ran.trans (.next rfl (.refl _))) rfl

end Rumoca.CEulerPreflight
