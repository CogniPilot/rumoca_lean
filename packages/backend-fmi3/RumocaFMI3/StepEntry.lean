import RumocaFMI3.StepGuards
import RumocaC.BodySuffix
import RumocaFMI3.BodyEmbedding
import RumocaFMI3.HistoryBodies

/-! Public CS input preparation and complete successful/null calls. Rejected
continuations, histories and actual-artifact composition remain separate. -/
noncomputable section
namespace Rumoca.FMI3.StepEntry
open CTree CMemory CBody
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def signature : Signature := ⟨"fmi3Status", "fmi3DoStep",
  [⟨"fmi3Instance", "instance", false⟩,
   ⟨"fmi3Float64", "currentCommunicationPoint", false⟩,
   ⟨"fmi3Float64", "communicationStepSize", false⟩,
   ⟨"fmi3Boolean", "noSetFMUStatePriorToCurrentPoint", false⟩,
   ⟨"fmi3Boolean *", "eventHandlingNeeded", false⟩,
   ⟨"fmi3Boolean *", "terminateSimulation", false⟩,
   ⟨"fmi3Boolean *", "earlyReturn", false⟩,
   ⟨"fmi3Float64 *", "lastSuccessfulTime", false⟩]⟩

structure Outputs where
  event : Option Address
  terminate : Option Address
  early : Option Address
  last : Option Address

structure Buffers where
  event : Address
  terminate : Address
  early : Address
  last : Address

def Buffers.outputs (buffers : Buffers) : Outputs :=
  ⟨some buffers.event, some buffers.terminate, some buffers.early, some buffers.last⟩

def bindings (handle : Option Address) (point step : BitVec 64) (flag : Bool)
    (outputs : Outputs) : List (String × Value) :=
  [("instance", .pointer handle), ("currentCommunicationPoint", .float64 point),
   ("communicationStepSize", .float64 step), ("noSetFMUStatePriorToCurrentPoint", boolean flag),
   ("eventHandlingNeeded", .pointer outputs.event), ("terminateSimulation", .pointer outputs.terminate),
   ("earlyReturn", .pointer outputs.early), ("lastSuccessfulTime", .pointer outputs.last)]

def arguments (handle : Option Address) (point step : BitVec 64) (flag : Bool)
    (outputs : Outputs) : List Value := (bindings handle point step flag outputs).map Prod.snd

def parameters (handle : Option Address) (point step : BitVec 64) (flag : Bool)
    (outputs : Outputs) : Locals :=
  (bindings handle point step flag outputs).foldr
    (fun entry env => CBody.bind env entry.1 entry.2) (fun _ => none)

def locals (env : Locals) (p : Address) := CBody.bind env "m" (.pointer (some p))

/-- Public input admission compares finite numerical values, including both
encodings of zero. The solver's separate duration policy is not imposed here. -/
def InputsValid (point step : BitVec 64) (time : Binary64.Value) : Prop :=
  match Float64.decode point, Float64.decode step with
  | .finite current, .finite duration =>
      Binary64.value current = Binary64.value time ∧ 0 < Binary64.value duration
  | _, _ => False

def inputCondition : Expr := Runtime.any [
  Runtime.negate (Runtime.finite (Runtime.v "currentCommunicationPoint")),
  Runtime.negate (Runtime.finite (Runtime.v "communicationStepSize")),
  Runtime.nev (Runtime.v "currentCommunicationPoint") (Runtime.field "time"),
  Runtime.le (Runtime.v "communicationStepSize") (Runtime.n 0)]

def inputGuard : Stmt := Runtime.reject inputCondition "Invalid communication point or step size"

def outputCode : List Stmt := [
  Runtime.pointerCheck ["eventHandlingNeeded", "terminateSimulation", "earlyReturn", "lastSuccessfulTime"],
  Runtime.out "eventHandlingNeeded" (Runtime.n 0), Runtime.out "terminateSimulation" (Runtime.n 0),
  Runtime.out "earlyReturn" (Runtime.n 0), Runtime.out "lastSuccessfulTime" (Runtime.field "time")]

def outputHeap (heap : Heap) (buffers : Buffers) (time : Binary64.Value) : Heap :=
  StateProofs.written
    (HistoryBodies.zero (HistoryBodies.zero (HistoryBodies.zero heap buffers.event) buffers.terminate) buffers.early)
    buffers.last (Binary64.toBits time).val

theorem body (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .doStep ++ outputCode ++
      inputGuard :: Runtime.doStep.drop 9 := rfl

variable [interface : CInterface]

structure Types : Prop where
  handle : interface.types "fmi3Instance" = some .pointer
  real : interface.types "fmi3Float64" = some .float64
  boolean : interface.types "fmi3Boolean" = some .boolean
  booleanPointer : interface.types "fmi3Boolean *" = some .pointer
  realPointer : interface.types "fmi3Float64 *" = some .pointer
  instancePointer : interface.types "Instance *" = some .pointer
  nullPointer : interface.types "void *" = some .pointer

theorem parameters_bound (types : Types) (handle : Option Address) (point step : BitVec 64)
    (flag : Bool) (outputs : Outputs) :
    CCalls.parameters signature.parameters (arguments handle point step flag outputs) =
      some (parameters handle point step flag outputs) := by
  cases flag <;> simp [signature, arguments, parameters, bindings, CCalls.parameters,
    CCalls.parameterType, CBody.cast, types.handle, types.real, types.boolean,
    types.booleanPointer, types.realPointer, convert, boolean, Value.truth, CBody.bind]

/-- Both supplied kind and mode are classified against the independent
reference lifecycle. This lemma is not tied to the old partial interface. -/
theorem lifecycle_run (types : Types) (env : Locals) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode) (rest : List Stmt)
    (handle : env "instance" = some (.pointer (some p))) (fresh : env "m" = none)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code)) :
    run 3 (.running (Runtime.require .doStep ++ rest) env heap) =
      some (.running ((if allowed .doStep kind mode then [] else
        [Runtime.fail "Call is not allowed in the current FMI state"]) ++ rest)
        (locals env p) heap) := by
  cases kind <;> cases mode <;>
    simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
      Runtime.reject, Runtime.branch, Runtime.ret, Runtime.negate, Runtime.v,
      Runtime.allowedExpression, Runtime.either, Runtime.both, Runtime.eqv,
      Runtime.field, Runtime.any, Runtime.mode, Runtime.n, permittedModes, allowed,
      Mode.code, Kind.code, locals, CBody.bind, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, resolve, constants,
      Expr.nullPointer, expressionCast, zeroLiteral, CBody.cast, types.instancePointer,
      types.nullPointer, convert, handle, fresh, kindValue, modeValue, comparison,
      boolean, Value.truth, Value.address]
  all_goals rfl

omit interface in
private theorem comparison_value (relation : Float64.Relation) (a b : Binary64.Value) :
    Float64.test relation (Binary64.toBits a).val (Binary64.toBits b).val =
      decide (relation.Holds (Binary64.value a) (Binary64.value b)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Float64.test_finite]

/-- Every raw public Float64 argument is classified, including NaN payloads,
infinities, signed zeros, mismatched clocks and nonpositive durations. -/
theorem input_condition_all (env : Locals) (heap : Heap) (p : Address)
    (point step : BitVec 64) (time : Binary64.Value)
    (instanceValue : env "m" = some (.pointer (some p)))
    (pointValue : env "currentCommunicationPoint" = some (.float64 point))
    (stepValue : env "communicationStepSize" = some (.float64 step))
    (clock : load heap (p.member "time") = some (.finite time)) :
    eval env heap inputCondition = some (boolean (decide (¬ InputsValid point step time))) := by
  by_cases pointFinite : point.toNat % Binary64.signPlace < Binary64.magnitudeCount
  · let current := Binary64.ofBits ⟨point, pointFinite⟩
    have pointEncoded : point = (Binary64.toBits current).val :=
      (congrArg Subtype.val (Binary64.toBits_ofBits ⟨point, pointFinite⟩)).symm
    by_cases stepFinite : step.toNat % Binary64.signPlace < Binary64.magnitudeCount
    · let duration := Binary64.ofBits ⟨step, stepFinite⟩
      have stepEncoded : step = (Binary64.toBits duration).val :=
        (congrArg Subtype.val (Binary64.toBits_ofBits ⟨step, stepFinite⟩)).symm
      rw [pointEncoded] at pointValue ⊢
      rw [stepEncoded] at stepValue ⊢
      have hp : (Value.float64 (Binary64.toBits current).val).isFinite = some true :=
        Value.isFinite_finite current
      have hs : (Value.float64 (Binary64.toBits duration).val).isFinite = some true :=
        Value.isFinite_finite duration
      by_cases same : Binary64.value current = Binary64.value time <;>
        by_cases positive : 0 < Binary64.value duration <;>
        simp [inputCondition, Runtime.any, Runtime.negate, Runtime.finite, Runtime.call,
          Runtime.v, Runtime.n, Runtime.nev, Runtime.field, Runtime.le, Runtime.either,
          CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, resolve, instanceValue, pointValue, stepValue, Value.address, clock,
          comparison, Value.finite, floatComparison, comparison_value,
          CIntegerConversions.integer_float64 0 (by decide +kernel),
          hp, hs, boolean, Value.truth, InputsValid, Float64.Relation.Holds,
          Binary64.ofSmallInt_value, same, positive, not_le.mpr, le_of_not_gt]
    · have hp : (Value.float64 point).isFinite = some true := by simp [Value.isFinite, pointFinite]
      have hs : (Value.float64 step).isFinite = some false := by simp [Value.isFinite, stepFinite]
      simp [inputCondition, Runtime.any, Runtime.negate, Runtime.finite, Runtime.call,
        Runtime.v, Runtime.n, Runtime.either, CBody.eval, CBody.evalWith, resolve, pointValue, stepValue,
        hp, hs, boolean, Value.truth, InputsValid, Float64.decode, pointFinite, stepFinite]
      split_ifs <;> simp_all
  · have hp : (Value.float64 point).isFinite = some false := by simp [Value.isFinite, pointFinite]
    simp [inputCondition, Runtime.any, Runtime.negate, Runtime.finite, Runtime.call,
      Runtime.v, Runtime.n, Runtime.either, CBody.eval, CBody.evalWith, resolve, pointValue, hp,
      boolean, Value.truth, InputsValid, Float64.decode, pointFinite]
    split_ifs <;> simp_all

theorem input_condition (env : Locals) (heap : Heap) (p : Address)
    (point time step : Binary64.Value)
    (instanceValue : env "m" = some (.pointer (some p)))
    (pointValue : env "currentCommunicationPoint" = some (.finite point))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (clock : load heap (p.member "time") = some (.finite time))
    (same : Binary64.value point = Binary64.value time) (positive : 0 < Binary64.value step) :
    eval env heap inputCondition = some (boolean false) := by
  simpa [InputsValid, same, positive] using
    input_condition_all env heap p (Binary64.toBits point).val (Binary64.toBits step).val time
      instanceValue pointValue stepValue clock

omit interface in
theorem float_ne_boolean (heap : Heap) (floating boolean : Address) (old : Option Value)
    (floatCell : heap floating = some ⟨.float64, true, old⟩)
    (boolCell : HistoryBodies.BoolWritable heap boolean) : floating ≠ boolean := by
  obtain ⟨previous, boolCell⟩ := boolCell
  intro same
  rw [same, boolCell] at floatCell
  cases floatCell

theorem outputs_run (env : Locals) (heap : Heap) (p : Address) (buffers : Buffers)
    (time : Binary64.Value) (old : Option Value) (rest : List Stmt)
    (instanceValue : env "m" = some (.pointer (some p)))
    (eventValue : env "eventHandlingNeeded" = some (.pointer (some buffers.event)))
    (terminateValue : env "terminateSimulation" = some (.pointer (some buffers.terminate)))
    (earlyValue : env "earlyReturn" = some (.pointer (some buffers.early)))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (clock : load heap (p.member "time") = some (.finite time))
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, old⟩)
    (outsideEvent : buffers.event.block ≠ p.block)
    (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block) :
    run 5 (.running (outputCode ++ rest) env heap) =
      some (.running rest env (outputHeap heap buffers time)) := by
  let h1 := HistoryBodies.zero heap buffers.event
  let h2 := HistoryBodies.zero h1 buffers.terminate
  let h3 := HistoryBodies.zero h2 buffers.early
  have storeEvent := HistoryBodies.zero_store event
  have storeTerminate := HistoryBodies.zero_store (HistoryBodies.zero_writable terminate buffers.event)
  have storeEarly := HistoryBodies.zero_store
    (HistoryBodies.zero_writable (HistoryBodies.zero_writable early buffers.event) buffers.terminate)
  have keptClock : load h3 (p.member "time") = some (.finite time) := by
    simpa [h3, h2, h1, load, HistoryBodies.zero_frame,
      HistoryBodies.field_ne_output p buffers.event "time" outsideEvent,
      HistoryBodies.field_ne_output p buffers.terminate "time" outsideTerminate,
      HistoryBodies.field_ne_output p buffers.early "time" outsideEarly] using clock
  have lastCell : h3 buffers.last = some ⟨.float64, true, old⟩ := by
    simp only [h3, h2, h1,
      HistoryBodies.zero_frame _ _ _ (float_ne_boolean heap _ _ old last early),
      HistoryBodies.zero_frame _ _ _ (float_ne_boolean heap _ _ old last terminate),
      HistoryBodies.zero_frame _ _ _ (float_ne_boolean heap _ _ old last event), last]
  have storeLast := store_float64 h3 buffers.last old (Binary64.toBits time).val lastCell
  simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, outputCode, Runtime.pointerCheck, Runtime.reject, Runtime.any,
    Runtime.branch, Runtime.out, Runtime.v, Runtime.n, Runtime.negate, Runtime.either,
    Runtime.field, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, CBody.lvalue, CBody.lvalueWith, resolve, instanceValue, eventValue, terminateValue,
    earlyValue, lastValue, Value.address, Value.truth, boolean,
    storeEvent, storeTerminate, storeEarly, show load h3 (p.member "time") = some (.finite time) from keptClock,
    storeLast, h1, h2, h3, outputHeap, Value.finite, StateProofs.written]

omit interface in
theorem output_frame (heap : Heap) (buffers : Buffers) (time : Binary64.Value) (query : Address)
    (event : query ≠ buffers.event) (terminate : query ≠ buffers.terminate)
    (early : query ≠ buffers.early) (last : query ≠ buffers.last) :
    outputHeap heap buffers time query = heap query := by
  simp only [outputHeap, StateProofs.written_frame _ _ _ _ last,
    HistoryBodies.zero_frame _ _ _ early, HistoryBodies.zero_frame _ _ _ terminate,
    HistoryBodies.zero_frame _ _ _ event]

omit interface in
theorem output_instance (heap : Heap) (buffers : Buffers) (time : Binary64.Value) (p query : Address)
    (event : buffers.event.block ≠ p.block) (terminate : buffers.terminate.block ≠ p.block)
    (early : buffers.early.block ≠ p.block) (last : buffers.last.block ≠ p.block)
    (inside : query.block = p.block) : outputHeap heap buffers time query = heap query := by
  have outside (address : Address) (separate : address.block ≠ p.block) : query ≠ address := by
    intro same
    exact separate ((congrArg Address.block same).symm.trans inside)
  exact output_frame heap buffers time query (outside _ event) (outside _ terminate)
    (outside _ early) (outside _ last)

/-- The shared nine-step input prefix is independent of the later numerical code. -/
theorem prefix_run_suffix (types : Types) (env : Locals)
    (heap : Heap) (p : Address) (buffers : Buffers) (point step : BitVec 64) (time : Binary64.Value)
    (oldOutput : Option Value)
    (handle : env "instance" = some (.pointer (some p))) (fresh : env "m" = none)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (pointValue : env "currentCommunicationPoint" = some (.float64 point))
    (stepValue : env "communicationStepSize" = some (.float64 step))
    (eventValue : env "eventHandlingNeeded" = some (.pointer (some buffers.event)))
    (terminateValue : env "terminateSimulation" = some (.pointer (some buffers.terminate)))
    (earlyValue : env "earlyReturn" = some (.pointer (some buffers.early)))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (clock : load heap (p.member "time") = some (.finite time))
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : buffers.event.block ≠ p.block) (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block) (outsideLast : buffers.last.block ≠ p.block) :
    ∀ tail : List Stmt,
    run 9 (.running ((Runtime.require .doStep ++ outputCode ++ [inputGuard]) ++ tail) env heap) =
      some (.running ((if InputsValid point step time then [] else [Runtime.fail
        "Invalid communication point or step size"]) ++ tail) (locals env p) (outputHeap heap buffers time)) := by
  have entered := lifecycle_run types env heap p .cs .step
    (outputCode ++ [inputGuard]) handle fresh kindValue modeValue
  simp only [allowed, permittedModes] at entered
  have setup := outputs_run (locals env p) heap p buffers time oldOutput
    [inputGuard] (by simp [locals, CBody.bind])
    (by simpa [locals, CBody.bind] using eventValue)
    (by simpa [locals, CBody.bind] using terminateValue)
    (by simpa [locals, CBody.bind] using earlyValue)
    (by simpa [locals, CBody.bind] using lastValue) clock event terminate early last
    outsideEvent outsideTerminate outsideEarly
  have clockAfter : load (outputHeap heap buffers time) (p.member "time") = some (.finite time) := by
    simpa only [load, output_instance heap buffers time p (p.member "time")
      outsideEvent outsideTerminate outsideEarly outsideLast rfl] using clock
  have condition := input_condition_all (locals env p) (outputHeap heap buffers time) p point step time
    (by simp [locals, CBody.bind]) (by simpa [locals, CBody.bind] using pointValue)
    (by simpa [locals, CBody.bind] using stepValue) clockAfter
  have checked : run 1 (.running [inputGuard] (locals env p) (outputHeap heap buffers time)) =
      some (.running (if InputsValid point step time then [] else [Runtime.fail
        "Invalid communication point or step size"]) (locals env p) (outputHeap heap buffers time)) := by
    by_cases valid : InputsValid point step time <;>
      simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, inputGuard, Runtime.reject, Runtime.branch, condition,
        valid, boolean, Value.truth]
  have isolated : run 9 (.running (Runtime.require .doStep ++ outputCode ++ [inputGuard]) env heap) =
      some (.running (if InputsValid point step time then [] else [Runtime.fail
        "Invalid communication point or step size"]) (locals env p) (outputHeap heap buffers time)) := by
    rw [List.append_assoc, show 9 = 3 + 6 from rfl, run_add, entered]
    change run 6 (.running (outputCode ++ [inputGuard]) (locals env p) heap) = _
    rw [show 6 = 5 + 1 from rfl, run_add, setup]
    exact checked
  intro tail
  exact run_running_suffix 9 _ _ tail _ _ _ _ isolated

def inputDestination (point step : BitVec 64) (time : Binary64.Value) : List Stmt :=
  (if InputsValid point step time then [] else
    [Runtime.fail "Invalid communication point or step size"]) ++ Runtime.doStep.drop 9

/-- The actual public prefix reaches admission or its input failure for every
raw point/step encoding, preserving the precise output initialization heap. -/
theorem prefix_run (types : Types) (model : Solve.FMI3Model source) (env : Locals)
    (heap : Heap) (p : Address) (buffers : Buffers) (point step : BitVec 64) (time : Binary64.Value)
    (oldOutput : Option Value)
    (handle : env "instance" = some (.pointer (some p))) (fresh : env "m" = none)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (pointValue : env "currentCommunicationPoint" = some (.float64 point))
    (stepValue : env "communicationStepSize" = some (.float64 step))
    (eventValue : env "eventHandlingNeeded" = some (.pointer (some buffers.event)))
    (terminateValue : env "terminateSimulation" = some (.pointer (some buffers.terminate)))
    (earlyValue : env "earlyReturn" = some (.pointer (some buffers.early)))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (clock : load heap (p.member "time") = some (.finite time))
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : buffers.event.block ≠ p.block) (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block) (outsideLast : buffers.last.block ≠ p.block) :
    run 9 (.running (Runtime.body model signature) env heap) =
      some (.running (inputDestination point step time) (locals env p) (outputHeap heap buffers time)) := by
  simpa only [body, inputDestination, List.append_assoc, List.singleton_append] using
    prefix_run_suffix types env heap p buffers point step time oldOutput handle fresh kindValue modeValue
      pointValue stepValue eventValue terminateValue earlyValue lastValue clock event terminate early last
      outsideEvent outsideTerminate outsideEarly outsideLast (Runtime.doStep.drop 9)

/-- Execute the public prefix through output initialization and source-independent
input admission. All later state/clock premises come from the original heap. -/
theorem ready_run (types : Types) (model : Solve.FMI3Model source) (env : Locals)
    (heap : Heap) (p : Address) (buffers : Buffers) (point time step : Binary64.Value)
    (oldOutput : Option Value)
    (handle : env "instance" = some (.pointer (some p))) (fresh : env "m" = none)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (pointValue : env "currentCommunicationPoint" = some (.finite point))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (eventValue : env "eventHandlingNeeded" = some (.pointer (some buffers.event)))
    (terminateValue : env "terminateSimulation" = some (.pointer (some buffers.terminate)))
    (earlyValue : env "earlyReturn" = some (.pointer (some buffers.early)))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (clock : load heap (p.member "time") = some (.finite time))
    (same : Binary64.value point = Binary64.value time) (positive : 0 < Binary64.value step)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : buffers.event.block ≠ p.block) (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block) (outsideLast : buffers.last.block ≠ p.block) :
    run 9 (.running (Runtime.body model signature) env heap) =
      some (.running (Runtime.doStep.drop 9) (locals env p) (outputHeap heap buffers time)) := by
  simpa [inputDestination, InputsValid, same, positive] using
    prefix_run types model env heap p buffers (Binary64.toBits point).val
      (Binary64.toBits step).val time oldOutput handle fresh kindValue modeValue
      pointValue stepValue eventValue terminateValue earlyValue lastValue clock
      event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast

/-- A null public handle terminates before reading any instance or output
buffer, for all raw floating arguments and nullable output addresses. -/
theorem null_call (types : Types) (program : CCalls.Events.Program E)
    (model : Solve.FMI3Model source) (heap : Heap) (point step : BitVec 64)
    (flag : Bool) (outputs : Outputs)
    (status : interface.types "fmi3Status" = some .int32)
    (error : interface.constants "fmi3Error" = some (.integer 3))
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments none point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply CCalls.Events.body_call_behaviors program (Runtime.function model signature) _
    (parameters none point step flag outputs) heap ⟨.integer 3, heap⟩ (.integer 3) 3
    defined (parameters_bound types none point step flag outputs) (BodyEmbedding.body_closed model signature)
  · change run 3 (.running (Runtime.body model signature) _ heap) = _
    rw [body]
    simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.require, Runtime.instancePrefix, Runtime.branch, Runtime.ret,
      Runtime.v, Expr.nullPointer, CBody.eval, CBody.evalWith, resolve, constants, parameters, bindings,
      CBody.bind, CBody.cast, expressionCast, zeroLiteral, types.instancePointer,
      types.nullPointer, convert, comparison, Value.truth, boolean, error]
  · simp [Runtime.function, CCalls.returnCast, signature, CBody.cast, status, convert]

/-- A complete successful public DoStep derives the post-validation storage
and solver count. Native floating environment and library bindings are supplied
explicitly; no successful target execution is an assumption. -/
theorem accepted_call (types : Types) (program : CCalls.Events.Program E)
    (model : Solve.FMI3Model source) (header : CFenv.Header)
    (heap : Heap) (p : Address) (buffers : Buffers) (x point time step : Binary64.Value)
    (flag : Bool) (stop : Option Binary64.Value) (oldTime oldOutput : Option Value)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (status : interface.types "fmi3Status" = some .int32)
    (helperTypes : ModelAdvance.Types)
    (ordinary : ∀ name ∈ ["fegetround", "floor", "model_advance"], interface.constants name = none)
    (macroBound : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (okBound : interface.constants "fmi3OK" = some (.integer 0))
    (rounding : program.externals "fegetround" = some (CMathCalls.roundingExternal integer
      header.nearest ⟨by have positive := header.nonnegative; omega, header.bounded⟩))
    (floorBound : program.externals "floor" = some (CMathCalls.floorExternal double))
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (clock : load heap (p.member "time") = some (.finite time))
    (same : Binary64.value point = Binary64.value time)
    (enabled : load heap (p.member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value → load heap (p.member "stop") = some (.finite value))
    (admitted : StepAdmission.AdmittedDuration step)
    (progress : Binary64.value time < Binary64.value (Binary64.roundedAdd time step))
    (withinStop : ∀ value, stop = some value → Binary64.value (Binary64.roundedAdd time step) ≤ Binary64.value value)
    (kernel : program.internal.kernel = CExecution.program model.solve)
    (helper : program.internal.definitions "model_advance" = some (.tree Runtime.helpers[2]))
    (sample : program.internal.definitions "rumoca_sample" = some (.kernel .sample))
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite x)⟩)
    (writableClock : heap (p.member "time") = some ⟨.float64, true, oldTime⟩)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : buffers.event.block ≠ p.block) (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block) (outsideLast : buffers.last.block ≠ p.block) :
    ∃ count : CStatements.Counter, 0 < count.val ∧ count.val ≤ 1000000 ∧
      Binary64.value step = (count.val : ℝ) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name
          (arguments (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs)
          heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0,
          StepAdvance.written (outputHeap heap buffers time) p buffers.last
            (model.solve.run x count.val) (Binary64.roundedAdd time step)⟩ := by
  let env := parameters (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs
  let later := locals env p
  let after := outputHeap heap buffers time
  have prepared := ready_run types model env heap p buffers point time step oldOutput
    (by simp [env, parameters, bindings, CBody.bind])
    (by simp [env, parameters, bindings, CBody.bind]) kindValue modeValue
    (by simp [env, parameters, bindings, CBody.bind, Value.finite])
    (by simp [env, parameters, bindings, CBody.bind, Value.finite])
    (by simp [env, parameters, bindings, CBody.bind, Buffers.outputs])
    (by simp [env, parameters, bindings, CBody.bind, Buffers.outputs])
    (by simp [env, parameters, bindings, CBody.bind, Buffers.outputs])
    (by simp [env, parameters, bindings, CBody.bind, Buffers.outputs])
    clock same admitted.1 event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast
  obtain ⟨localTypes, entered⟩ := CCalls.Events.body_prefix_reaches program
    (Runtime.function model signature) _ env later heap after (Runtime.doStep.drop 9) .done 9
    defined (parameters_bound types _ _ _ _ _) (BodyEmbedding.body_closed model signature) prepared
  have framed (query : Address) (inside : query.block = p.block) : after query = heap query :=
    output_instance heap buffers time p query outsideEvent outsideTerminate outsideEarly outsideLast inside
  have loaded (name : String) : load after (p.member name) = load heap (p.member name) := by
    simp only [load, framed (p.member name) rfl]
  have lastStored : after buffers.last =
      some ⟨.float64, true, some (.finite time)⟩ := by
    simp [after, outputHeap, StateProofs.written, Value.finite]
  obtain ⟨count, positive, bounded, duration, executed⟩ := StepGuards.accepted_execution program model.solve
    header later localTypes after p buffers.last x time step stop oldTime (some (.finite time))
    integer double status helperTypes
    (by intro name member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [later, locals, env, parameters, bindings, CBody.bind])
    ordinary macroBound okBound rounding floorBound
    (by simp [later, locals, CBody.bind])
    (by simp [later, locals, env, parameters, bindings, CBody.bind, Value.finite])
    (by simp [later, locals, env, parameters, bindings, CBody.bind, Buffers.outputs])
    ((loaded "time").trans clock) ((loaded "stopDefined").trans enabled)
    (fun value chosen => (loaded "stop").trans (limit value chosen)) admitted progress withinStop kernel helper sample
    ((framed (StateProofs.stateAddress p) rfl).trans stored)
    ((framed (p.member "time") rfl).trans writableClock) lastStored outsideLast
  refine ⟨count, positive, bounded, duration, ?_⟩
  intro behavior
  exact (CCalls.Events.internal_prefix_behaviors program entered behavior).trans (executed behavior)

omit interface in
private theorem zero_preserves (heap : Heap) (query target : Address)
    (stored : heap query = some ⟨.boolean, true, some (.integer 0)⟩) :
    HistoryBodies.zero heap target query = some ⟨.boolean, true, some (.integer 0)⟩ := by
  by_cases same : query = target
  · simp [HistoryBodies.zero, same]
  · exact (HistoryBodies.zero_frame heap target query same).trans stored

omit interface in
/-- Boolean aliases retain their common zero value. A Float64 output cannot
alias those Boolean cells in the admitted typed object-memory profile. -/
theorem output_values (heap : Heap) (buffers : Buffers) (time : Binary64.Value)
    (old : Option Value) (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, old⟩) :
    outputHeap heap buffers time buffers.event = some ⟨.boolean, true, some (.integer 0)⟩ ∧
    outputHeap heap buffers time buffers.terminate = some ⟨.boolean, true, some (.integer 0)⟩ ∧
    outputHeap heap buffers time buffers.early = some ⟨.boolean, true, some (.integer 0)⟩ ∧
    outputHeap heap buffers time buffers.last = some ⟨.float64, true, some (.finite time)⟩ := by
  have first : HistoryBodies.zero heap buffers.event buffers.event =
      some ⟨.boolean, true, some (.integer 0)⟩ := by simp [HistoryBodies.zero]
  have second : HistoryBodies.zero (HistoryBodies.zero heap buffers.event) buffers.terminate buffers.terminate =
      some ⟨.boolean, true, some (.integer 0)⟩ := by simp [HistoryBodies.zero]
  have third : HistoryBodies.zero
      (HistoryBodies.zero (HistoryBodies.zero heap buffers.event) buffers.terminate) buffers.early buffers.early =
      some ⟨.boolean, true, some (.integer 0)⟩ := by simp [HistoryBodies.zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (StateProofs.written_frame _ _ _ _ (float_ne_boolean heap _ _ old last event).symm).trans
      (zero_preserves _ _ _ (zero_preserves _ _ _ first))
  · exact (StateProofs.written_frame _ _ _ _ (float_ne_boolean heap _ _ old last terminate).symm).trans
      (zero_preserves _ _ _ second)
  · exact (StateProofs.written_frame _ _ _ _ (float_ne_boolean heap _ _ old last early).symm).trans third
  · simp [outputHeap, StateProofs.written, Value.finite]

omit interface in
theorem call_frame (heap : Heap) (p : Address) (buffers : Buffers) (time state nextTime : Binary64.Value)
    (query : Address) (stateOther : query ≠ StateProofs.stateAddress p)
    (clockOther : query ≠ p.member "time") (event : query ≠ buffers.event)
    (terminate : query ≠ buffers.terminate) (early : query ≠ buffers.early) (last : query ≠ buffers.last) :
    StepAdvance.written (outputHeap heap buffers time) p buffers.last state nextTime query = heap query :=
  (StepAdvance.written_frame _ _ _ _ _ _ stateOther clockOther last).trans
    (output_frame heap buffers time query event terminate early last)

omit interface in
theorem final_values (heap : Heap) (p : Address) (buffers : Buffers)
    (time state nextTime : Binary64.Value) (old : Option Value)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, old⟩)
    (outsideEvent : buffers.event.block ≠ p.block) (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block) (outsideLast : buffers.last.block ≠ p.block) :
    let after := StepAdvance.written (outputHeap heap buffers time) p buffers.last state nextTime
    after buffers.event = some ⟨.boolean, true, some (.integer 0)⟩ ∧
    after buffers.terminate = some ⟨.boolean, true, some (.integer 0)⟩ ∧
    after buffers.early = some ⟨.boolean, true, some (.integer 0)⟩ ∧
    after (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state)⟩ ∧
    after (p.member "time") = some ⟨.float64, true, some (.finite nextTime)⟩ ∧
    after buffers.last = some ⟨.float64, true, some (.finite nextTime)⟩ := by
  obtain ⟨eventStored, terminateStored, earlyStored, _⟩ := output_values heap buffers time old event terminate early last
  have kept (query : Address) (outside : query.block ≠ p.block) (other : query ≠ buffers.last) :
      StepAdvance.written (outputHeap heap buffers time) p buffers.last state nextTime query =
        outputHeap heap buffers time query := by
    apply StepAdvance.written_frame _ _ _ _ _ _ _ _ other
    · intro same
      apply outside
      simpa [StateProofs.stateAddress, Address.member] using congrArg Address.block same
    · intro same
      apply outside
      simpa [Address.member] using congrArg Address.block same
  exact ⟨(kept _ outsideEvent (float_ne_boolean heap _ _ old last event).symm).trans eventStored,
    (kept _ outsideTerminate (float_ne_boolean heap _ _ old last terminate).symm).trans terminateStored,
    (kept _ outsideEarly (float_ne_boolean heap _ _ old last early).symm).trans earlyStored,
    StepAdvance.written_values _ p buffers.last state nextTime outsideLast⟩

end Rumoca.FMI3.StepEntry
end
