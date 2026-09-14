import RumocaFMI3.ModelAdvance
import RumocaC.NamedCallSites
import RumocaC.CallCasts
import RumocaC.IntegerConversions

noncomputable section
namespace Rumoca.FMI3.StepAdvance
open CTree CMemory CCalls
variable [interface : CInterface]
set_option maxRecDepth 10000

def finalWrites : List Stmt :=
  [Runtime.put "time" (Runtime.v "next"),
   Runtime.out "lastSuccessfulTime" (Runtime.v "next"), Runtime.ok]

def code : List Stmt :=
  .eval (Runtime.call "model_advance" [.address (Runtime.field "model"),
    .cast "uint64_t" (Runtime.v "communicationStepSize")]) :: finalWrites

omit interface in
theorem actual_tail : Runtime.doStep.drop 16 = code := rfl

def written (heap : Heap) (p output : Address) (state time : Binary64.Value) : Heap :=
  StateProofs.written
    (StateProofs.written
      (StateProofs.written heap (StateProofs.stateAddress p) (Binary64.toBits state).val)
      (p.member "time") (Binary64.toBits time).val)
    output (Binary64.toBits time).val

omit interface in
theorem time_ne_state (p : Address) : p.member "time" ≠ StateProofs.stateAddress p := by
  intro same
  have lengths := congrArg (fun address : Address => address.members.length) same
  simp [StateProofs.stateAddress, Address.member] at lengths

/-- Execute the actual final solver call and output stores. Admission and the
relation between `next` and the communication increment are proved separately;
no successful solver execution is supplied as a premise. -/
theorem reaches (program : Events.Program E) (model : Solve.Model source)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (p output : Address) (x step next : Binary64.Value) (count : CStatements.Counter)
    (oldTime oldOutput : Option Value) (stack : Typed.Continuation)
    (helperTypes : ModelAdvance.Types)
    (statusType : interface.types "fmi3Status" = some .int32)
    (global : interface.constants "model_advance" = none)
    (unshadowed : env "model_advance" = none)
    (instanceValue : env "m" = some (.pointer (some p)))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (nextValue : env "next" = some (.finite next))
    (outputValue : env "lastSuccessfulTime" = some (.pointer (some output)))
    (okValue : CBody.resolve env "fmi3OK" = some (.integer 0))
    (duration : Binary64.value step = (count.val : ℝ))
    (kernel : program.internal.kernel = CExecution.program model)
    (helper : program.internal.definitions "model_advance" = some (.tree Runtime.helpers[2]))
    (sample : program.internal.definitions "rumoca_sample" = some (.kernel .sample))
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite x)⟩)
    (clock : heap (p.member "time") = some ⟨.float64, true, oldTime⟩)
    (buffer : heap output = some ⟨.float64, true, oldOutput⟩)
    (outside : output.block ≠ p.block) :
    Transition.Reaches (fun s t => Events.internalNext program s = some t)
      (.body (.running code env types heap) "fmi3Status" stack)
      (.returning (.integer 0) (written heap p output (model.run x count.val) next) stack) := by
  have converted : convert .size (.finite step) = some (.integer count.val) := by
    apply (CIntegerConversions.finite_size_iff step (count.val : Int)).mpr
    refine ⟨(Binary64.truncateInteger_exact step (count.val : Int) ?_).symm,
      Int.natCast_nonneg _, ?_⟩
    · simpa only [Int.cast_natCast] using duration
    · exact_mod_cast count.isLt
  let stateHeap := StateProofs.written heap (StateProofs.stateAddress p)
    (Binary64.toBits (model.run x count.val)).val
  let timeHeap := StateProofs.written stateHeap (p.member "time") (Binary64.toBits next).val
  let saved := Typed.Continuation.caller .discard finalWrites env types "fmi3Status" stack
  have outputState : output ≠ StateProofs.stateAddress p := by
    intro same
    apply outside
    simpa [StateProofs.stateAddress, Address.member] using congrArg Address.block same
  have outputTime : output ≠ p.member "time" := by
    intro same
    apply outside
    simpa [Address.member] using congrArg Address.block same
  have stateClock : stateHeap (p.member "time") = some ⟨.float64, true, oldTime⟩ :=
    (StateProofs.written_frame _ _ _ _ (time_ne_state p)).trans clock
  have timeOutput : timeHeap output = some ⟨.float64, true, oldOutput⟩ :=
    (StateProofs.written_frame _ _ _ _ outputTime).trans
      ((StateProofs.written_frame _ _ _ _ outputState).trans buffer)
  refine .next (t := .calling "model_advance"
    [.pointer (some (p.member "model")), .integer count.val] heap saved) ?_ ?_
  · simp [Events.internalNext, Typed.nextWith, CLoops.next, CLoops.eval, CBody.eval,
      code, Runtime.call, Runtime.field, Runtime.v, Events.enterCall, Events.resolve,
      Indirect.operand, Indirect.resolve, CBody.resolve, CBody.constants,
      CBody.lvalue, CBody.expressionCast, CBody.zeroLiteral, CBody.cast, helperTypes.count,
      unshadowed, global, instanceValue, stepValue, converted, Value.address, arguments, saved]
  refine (ModelAdvance.advance_reaches program helperTypes model kernel helper sample
    heap (p.member "model") x count stored saved).trans (.next (t :=
      .body (.running finalWrites env types stateHeap) "fmi3Status" stack) ?_ ?_)
  · rfl
  refine .next (t := .body (.running (finalWrites.drop 1) env types timeHeap) "fmi3Status" stack) ?_ ?_
  · apply Events.body_step
    simp [CLoops.next, CLoops.eval, CBody.eval, CBody.lvalue, CBody.resolve,
      finalWrites, Runtime.put, Runtime.field, Runtime.v, nextValue, instanceValue,
      Value.address, Value.finite, store_float64 stateHeap (p.member "time") _ _ stateClock,
      timeHeap, StateProofs.written]
  refine .next (t := .body (.running [Runtime.ok] env types
    (written heap p output (model.run x count.val) next)) "fmi3Status" stack) ?_ ?_
  · apply Events.body_step
    simp [CLoops.next, CLoops.eval, CBody.eval, CBody.lvalue, CBody.resolve,
      finalWrites, Runtime.out, Runtime.v, nextValue, outputValue, Value.address, Value.finite,
      store_float64 timeHeap output _ _ timeOutput, written, StateProofs.written]
    rfl
  exact Events.expression_return program env types _ (Runtime.v "fmi3OK") []
    "fmi3Status" stack (.integer 0) (.integer 0)
    (by simpa [CLoops.eval, CBody.eval, Runtime.v] using okValue)
    (CCalls.Casts.valueReturn "fmi3Status" _ _ (by decide)
      (CCalls.Casts.named "fmi3Status" .int32 _ _ statusType rfl))

omit interface in
theorem written_frame (heap : Heap) (p output query : Address) (state time : Binary64.Value)
    (otherState : query ≠ StateProofs.stateAddress p)
    (otherTime : query ≠ p.member "time") (otherOutput : query ≠ output) :
    written heap p output state time query = heap query := by
  simp only [written, StateProofs.written_frame _ _ _ _ otherOutput,
    StateProofs.written_frame _ _ _ _ otherTime, StateProofs.written_frame _ _ _ _ otherState]

omit interface in
theorem written_values (heap : Heap) (p output : Address) (state time : Binary64.Value)
    (outside : output.block ≠ p.block) :
    written heap p output state time (StateProofs.stateAddress p) =
      some ⟨.float64, true, some (.finite state)⟩ ∧
    written heap p output state time (p.member "time") =
      some ⟨.float64, true, some (.finite time)⟩ ∧
    written heap p output state time output = some ⟨.float64, true, some (.finite time)⟩ := by
  have stateOutput : StateProofs.stateAddress p ≠ output := by
    intro same
    apply outside
    simpa [StateProofs.stateAddress, Address.member] using congrArg Address.block same.symm
  have timeOutput : p.member "time" ≠ output := by
    intro same
    apply outside
    simpa [Address.member] using congrArg Address.block same.symm
  simp [written, StateProofs.written, replace, stateOutput, timeOutput,
    (time_ne_state p).symm, Value.finite]

end Rumoca.FMI3.StepAdvance
end
