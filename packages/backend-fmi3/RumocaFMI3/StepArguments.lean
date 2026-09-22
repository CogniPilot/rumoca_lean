import RumocaFMI3.StepErrors
import RumocaC.LiteralPoolContents

/-! Complete public CS argument errors, including the exact output writes
before numerical rejection. Rounding, stop and discard paths remain separate. -/
noncomputable section
namespace Rumoca.FMI3.StepArguments
open CTree CMemory CBody
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def MissingOutput (outputs : StepEntry.Outputs) : Prop :=
  outputs.event = none ∨ outputs.terminate = none ∨ outputs.early = none ∨ outputs.last = none

section Generic
variable [CInterface]

/-- One reusable interpretation of the pointer guard for any parameter list. -/
theorem pointer_condition (names : List String) (addresses : String → Option Address)
    (env : Locals) (heap : Heap)
    (bound : ∀ name ∈ names, eval env heap (Runtime.v name) = some (.pointer (addresses name))) :
    eval env heap (Runtime.any (names.map fun name => Runtime.negate (Runtime.v name))) =
      some (boolean (names.any fun name => (addresses name).isNone)) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    have head := bound name (by simp)
    have tail := ih (fun n member => bound n (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, Runtime.any, List.foldr_cons] at *
    change ((eval env heap (.not (Runtime.v name))).bind fun a => a.truth.bind fun b =>
      if b then some (boolean true) else
        (eval env heap ((names.map fun n => Runtime.negate (Runtime.v n)).foldr
          Runtime.either (Runtime.n 0))).bind fun c =>
          c.truth.bind fun d => some (boolean d)) = _
    have negated : eval env heap (.not (Runtime.v name)) =
        some (boolean (addresses name).isNone) := by
      simp only [CBody.eval, CBody.evalWith, head]
      cases addresses name <;> rfl
    rw [negated, tail]
    cases value : addresses name <;> simp [List.any_cons, value, Value.truth, boolean]

theorem pointerCheck_run (names : List String) (addresses : String → Option Address)
    (env : Locals) (heap : Heap) (tail : List Stmt)
    (bound : ∀ name ∈ names, eval env heap (Runtime.v name) = some (.pointer (addresses name))) :
    run 1 (.running (Runtime.pointerCheck names :: tail) env heap) =
      some (.running ((if names.any (fun name => (addresses name).isNone) then
        [Runtime.fail "Missing output pointer"] else []) ++ tail) env heap) := by
  have condition := pointer_condition names addresses env heap bound
  cases found : names.any (fun name => (addresses name).isNone) <;>
    simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.pointerCheck, Runtime.reject, Runtime.branch,
      condition, found, Value.truth, boolean]


/-- Every function with the shared step entry rejects a null output pointer
before reading its clock or accessing any caller output cell. -/
theorem outputs_prefix_for_tail (types : StepEntry.Types) (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard :: tail)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (heap : Heap) (p : Address) (point step : BitVec 64) (flag : Bool)
    (outputs : StepEntry.Outputs)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (missing : MissingOutput outputs) :
    GuardedCalls.FailurePrefix fn (StepEntry.arguments (some p) point step flag outputs)
      heap p "Missing output pointer" heap := by
  let env := StepEntry.parameters (some p) point step flag outputs
  let later := StepEntry.locals env p
  let rest := StepEntry.outputCode.drop 1 ++ StepEntry.inputGuard :: tail
  let addresses : String → Option Address := fun name =>
    if name = "eventHandlingNeeded" then outputs.event else
    if name = "terminateSimulation" then outputs.terminate else
    if name = "earlyReturn" then outputs.early else outputs.last
  have entered := StepEntry.lifecycle_run types env heap p .cs .step
    (StepEntry.outputCode ++ StepEntry.inputGuard :: tail)
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
  simp only [allowed, permittedModes] at entered
  have bound : ∀ name ∈ ["eventHandlingNeeded", "terminateSimulation", "earlyReturn", "lastSuccessfulTime"],
      eval later heap (Runtime.v name) = some (.pointer (addresses name)) := by
    intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [later, env, StepEntry.locals, StepEntry.parameters, StepEntry.bindings,
        CBody.bind, Runtime.v, CBody.eval, CBody.evalWith, resolve, addresses]
  have missingAny : ["eventHandlingNeeded", "terminateSimulation", "earlyReturn", "lastSuccessfulTime"].any
      (fun name => (addresses name).isNone) = true := by
    rcases missing with h | h | h | h <;> simp [addresses, h]
  have checked := pointerCheck_run
    ["eventHandlingNeeded", "terminateSimulation", "earlyReturn", "lastSuccessfulTime"]
    addresses later heap rest bound
  simp only [missingAny, ↓reduceIte, List.singleton_append] at checked
  refine ⟨by rw [signature]; rfl, closed, env, later, rest, 4, ?_, ?_, ?_, ?_⟩
  · rw [signature]
    exact StepEntry.parameters_bound types _ _ _ _ _
  · rw [body, List.append_assoc, show 4 = 3 + 1 from rfl, run_add, entered]
    exact checked
  · simp [later, StepEntry.locals, env, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [later, StepEntry.locals, CBody.bind, resolve]


end Generic

/-- Missing outputs are rejected before any output access or numeric check.
This prefix needs no output-buffer storage and preserves the whole heap. -/
theorem outputs_prefix (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (heap : Heap) (p : Address) (point step : BitVec 64) (flag : Bool)
    (outputs : StepEntry.Outputs)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (missing : MissingOutput outputs) :
    @GuardedCalls.FailurePrefix context.target (Runtime.function model StepEntry.signature)
      (StepEntry.arguments (some p) point step flag outputs) heap p "Missing output pointer" heap := by
  letI : CInterface := context.target
  exact outputs_prefix_for_tail (StepErrors.types context) (Runtime.function model StepEntry.signature)
    (Runtime.doStep.drop 9) rfl (StepEntry.body model) (BodyEmbedding.body_closed model StepEntry.signature)
    heap p point step flag outputs kindValue modeValue missing

/-- Writable public output cells outside the instance object. Boolean outputs
may alias; the type of the Float64 cell excludes Boolean/Float64 aliasing. -/
structure Storage (heap : Heap) (p : Address) (buffers : StepEntry.Buffers) : Prop where
  event : HistoryBodies.BoolWritable heap buffers.event
  terminate : HistoryBodies.BoolWritable heap buffers.terminate
  early : HistoryBodies.BoolWritable heap buffers.early
  last : ∃ old, heap buffers.last = some ⟨.float64, true, old⟩
  outsideEvent : buffers.event.block ≠ p.block
  outsideTerminate : buffers.terminate.block ≠ p.block
  outsideEarly : buffers.early.block ≠ p.block
  outsideLast : buffers.last.block ≠ p.block

theorem Storage.instance_frame (stored : Storage heap p buffers) (time : Binary64.Value)
    (query : Address) (inside : query.block = p.block) :
    StepEntry.outputHeap heap buffers time query = heap query :=
  StepEntry.output_instance heap buffers time p query stored.outsideEvent stored.outsideTerminate
    stored.outsideEarly stored.outsideLast inside

theorem Storage.load_field (stored : Storage heap p buffers) (time : Binary64.Value) (name : String) :
    load (StepEntry.outputHeap heap buffers time) (p.member name) = load heap (p.member name) := by
  simp only [load, stored.instance_frame time (p.member name) rfl]

def inputMessage : String := "Invalid communication point or step size"

/-- The shared input rejection prefix is independent of the numerical tail. -/
theorem input_prefix_for_tail [CInterface] (types : StepEntry.Types) (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard :: tail)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
    (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (clock : load heap (p.member "time") = some (.finite time))
    (stored : Storage heap p buffers) (invalid : ¬ StepEntry.InputsValid point step time) :
    GuardedCalls.FailurePrefix fn (StepEntry.arguments (some p) point step flag buffers.outputs)
      heap p inputMessage (StepEntry.outputHeap heap buffers time) := by
  let env := StepEntry.parameters (some p) point step flag buffers.outputs
  let later := StepEntry.locals env p
  obtain ⟨old, last⟩ := stored.last
  have ran := StepEntry.prefix_run_suffix types env heap p buffers point step time old
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    clock stored.event stored.terminate stored.early last stored.outsideEvent
    stored.outsideTerminate stored.outsideEarly stored.outsideLast tail
  refine ⟨by rw [signature]; rfl, closed, env, later, tail, 9, ?_, ?_, ?_, ?_⟩
  · rw [signature]
    exact StepEntry.parameters_bound types _ _ _ _ _
  · simpa only [body, List.append_assoc, List.singleton_append, invalid, ↓reduceIte,
      inputMessage] using ran
  · simp [later, StepEntry.locals, env, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [later, StepEntry.locals, CBody.bind, resolve]

/-- Every invalid raw numeric argument pair reaches the emitted failure after
output initialization. Every instance field is preserved. -/
theorem input_prefix (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
    (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (clock : load heap (p.member "time") = some (.finite time))
    (stored : Storage heap p buffers) (invalid : ¬ StepEntry.InputsValid point step time) :
    @GuardedCalls.FailurePrefix context.target (Runtime.function model StepEntry.signature)
      (StepEntry.arguments (some p) point step flag buffers.outputs) heap p inputMessage
      (StepEntry.outputHeap heap buffers time) := by
  letI : CInterface := context.target
  exact input_prefix_for_tail (StepErrors.types context) (Runtime.function model StepEntry.signature)
    (Runtime.doStep.drop 9) rfl (StepEntry.body model) (BodyEmbedding.body_closed model StepEntry.signature)
    heap p buffers point step time flag kindValue modeValue clock stored invalid

/-- The complete suppressed-error heap retains every instance cell except
the required mode change; this includes the numerical state and clock. -/
theorem input_instance_frame (stored : Storage heap p buffers) (time : Binary64.Value)
    (query : Address) (inside : query.block = p.block) (other : query ≠ p.member "mode") :
    LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated query = heap query :=
  (LifecycleBodies.write_frame _ p query .terminated other).trans (stored.instance_frame time query inside)

/-- Nullability is exhaustively classified; the nonmissing case supplies all
four addresses. Writable storage remains a separate condition. -/
theorem output_cases (outputs : StepEntry.Outputs) :
    MissingOutput outputs ∨ ∃ buffers : StepEntry.Buffers, outputs = buffers.outputs := by
  rcases outputs with ⟨event, terminate, early, last⟩
  cases event <;> cases terminate <;> cases early <;> cases last <;>
    simp [MissingOutput, StepEntry.Buffers.outputs]
  exact ⟨⟨_, _, _, _⟩, rfl, rfl, rfl, rfl⟩

theorem outputs_suppressed {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs)
      (logger : Option Address) (logging : Bool),
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "Missing output pointer" = some message →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      MissingOutput outputs → (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := context.target
  intro program heap p message point step flag outputs logger logging
    defined helper messageBound kindValue modeCell loggerValue loggingValue missing suppressed behavior
  have certified := StepArguments.outputs_prefix context model heap p point step flag outputs kindValue
    (by simp [load, modeCell, convert]) missing
  exact StaticErrors.prefix_suppressed_behaviors context program (Runtime.function model StepEntry.signature)
    (StepEntry.arguments (some p) point step flag outputs) heap heap p message "Missing output pointer"
    _ logger logging certified defined helper messageBound modeCell loggerValue loggingValue suppressed behavior

theorem outputs_logged {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message category logger : Address)
      (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals "Missing output pointer" = some message → literals "logStatus" = some category →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      MissingOutput outputs → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program heap p message category logger point step flag outputs environment name foreign
    defined helper messageBound categoryBound address external prototype kindValue modeCell
    loggerValue loggingValue environmentValue missing behavior
  have certified := StepArguments.outputs_prefix context model heap p point step flag outputs kindValue
    (by simp [load, modeCell, convert]) missing
  exact StaticErrors.prefix_all_behaviors context program (Runtime.function model StepEntry.signature)
    (StepEntry.arguments (some p) point step flag outputs) heap heap p message category logger
    "Missing output pointer" name environment _ foreign certified defined helper messageBound address external
    prototype categoryBound modeCell loggerValue loggingValue environmentValue behavior

theorem input_suppressed {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (logger : Option Address) (logging : Bool),
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals inputMessage = some message →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → Storage heap p buffers →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      ¬ StepEntry.InputsValid point step time → (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩ := by
  letI : CInterface := context.target
  intro program heap p message buffers point step time flag logger logging
    defined helper messageBound kindValue modeCell clock stored loggerValue loggingValue invalid suppressed behavior
  have certified := input_prefix context model heap p buffers point step time flag kindValue
    (by simp [load, modeCell, convert]) clock stored invalid
  exact StaticErrors.prefix_suppressed_behaviors context program (Runtime.function model StepEntry.signature)
    (StepEntry.arguments (some p) point step flag buffers.outputs) heap (StepEntry.outputHeap heap buffers time)
    p message inputMessage _ logger logging certified defined helper messageBound
    ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue)
    ((stored.load_field time "logging").trans loggingValue) suppressed behavior

theorem input_logged {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message category logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals inputMessage = some message → literals "logStatus" = some category →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → Storage heap p buffers →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      ¬ StepEntry.InputsValid point step time → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧
        behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program heap p message category logger buffers point step time flag environment name foreign
    defined helper messageBound categoryBound address external prototype kindValue modeCell clock stored
    loggerValue loggingValue environmentValue invalid behavior
  have certified := input_prefix context model heap p buffers point step time flag kindValue
    (by simp [load, modeCell, convert]) clock stored invalid
  exact StaticErrors.prefix_all_behaviors context program (Runtime.function model StepEntry.signature)
    (StepEntry.arguments (some p) point step flag buffers.outputs) heap (StepEntry.outputHeap heap buffers time)
    p message category logger inputMessage name environment _ foreign certified defined helper messageBound
    address external prototype categoryBound ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue) ((stored.load_field time "logging").trans loggingValue)
    ((stored.load_field time "environment").trans environmentValue) behavior

/-- Admission supplies the exact public body state after output initialization,
for every valid pair of raw point/step encodings and the supplied caller buffers. -/
theorem ready_prefix (context : ErrorContext literals) (model : Solve.FMI3Model source) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool),
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → Storage heap p buffers →
      StepEntry.InputsValid point step time →
      ∃ types, Transition.Events.Prefix (CCalls.Events.machine program)
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) []
        (.body (.running (Runtime.doStep.drop 9)
          (StepEntry.locals (StepEntry.parameters (some p) point step flag buffers.outputs) p)
          types (StepEntry.outputHeap heap buffers time)) "fmi3Status" .done) := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag defined kindValue modeValue clock stored valid
  let env := StepEntry.parameters (some p) point step flag buffers.outputs
  let later := StepEntry.locals env p
  obtain ⟨old, last⟩ := stored.last
  have ran := StepEntry.prefix_run (StepErrors.types context) model env heap p buffers point step time old
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    clock stored.event stored.terminate stored.early last stored.outsideEvent
    stored.outsideTerminate stored.outsideEarly stored.outsideLast
  simp only [StepEntry.inputDestination, valid, ↓reduceIte, List.nil_append] at ran
  obtain ⟨types, entered⟩ := CCalls.Events.body_prefix_reaches program
    (Runtime.function model StepEntry.signature) _ env later heap (StepEntry.outputHeap heap buffers time)
    (Runtime.doStep.drop 9) .done 9 defined (StepEntry.parameters_bound (StepErrors.types context) _ _ _ _ _)
    (BodyEmbedding.body_closed model StepEntry.signature) ran
  exact ⟨types, CCalls.Events.internal_path program entered⟩

/-- Invalid raw inputs initialize the outputs, terminate the instance and return
Error with logging disabled, under any checked error context. -/
theorem context_input_silent_for_tail {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (tail : List Stmt),
    fn.signature = StepEntry.signature →
    fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard :: tail →
    fn.body.all CBodyEmbedding.closedBlocks = true →
    ∀ (heap : Heap) (p message : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool) (logger : Option Address),
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals inputMessage = some message →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    Storage heap p buffers →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    ¬ StepEntry.InputsValid point step time → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
        heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩ := by
  letI : CInterface := context.target
  intro program fn tail signature body closed heap p message buffers point step time flag logger
    defined helper messageBound kindValue modeCell clock stored loggerValue loggingValue invalid behavior
  have certified := input_prefix_for_tail (StepErrors.types context) fn tail signature body closed
    heap p buffers point step time flag kindValue
    (by simp [load, modeCell, convert]) clock stored invalid
  exact StaticErrors.prefix_suppressed_behaviors context program fn
    (StepEntry.arguments (some p) point step flag buffers.outputs)
    heap (StepEntry.outputHeap heap buffers time) p message inputMessage
    (some (.integer 4)) logger false certified defined helper messageBound
    ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue)
    ((stored.load_field time "logging").trans loggingValue) (Or.inr rfl) behavior

/-- Invalid raw inputs initialize the outputs and terminate the instance before
logging under any checked error context. All represented callback outcomes and
the absence-of-outcome wrong behavior are retained. -/
theorem context_input_logged_for_tail {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (tail : List Stmt),
    fn.signature = StepEntry.signature →
    fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard :: tail →
    fn.body.all CBodyEmbedding.closedBlocks = true →
    ∀ (heap : Heap) (p message category logger : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals inputMessage = some message →
    program.addresses logger = some name →
    program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    literals "logStatus" = some category →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    Storage heap p buffers →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    ¬ StepEntry.InputsValid point step time → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
        heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated)
        events value after ∧ behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated)
        events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program fn tail signature body closed heap p message category logger buffers point step time flag
    environment name foreign defined helper messageBound address external prototype literal
    kindValue modeCell clock stored loggerValue loggingValue environmentValue invalid behavior
  have certified := input_prefix_for_tail (StepErrors.types context) fn tail signature body closed
    heap p buffers point step time flag kindValue
    (by simp [load, modeCell, convert]) clock stored invalid
  exact StaticErrors.prefix_all_behaviors context program fn
    (StepEntry.arguments (some p) point step flag buffers.outputs)
    heap (StepEntry.outputHeap heap buffers time) p message category logger inputMessage name
    environment (some (.integer 4)) foreign certified defined helper messageBound
    address external prototype literal
    ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue)
    ((stored.load_field time "logging").trans loggingValue)
    ((stored.load_field time "environment").trans environmentValue) behavior

theorem input_missing_context {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (tail : List Stmt),
      fn.signature = StepEntry.signature →
      fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard :: tail →
      fn.body.all CBodyEmbedding.closedBlocks = true →
      ∀ (heap : Heap) (p message : Address) (buffers : StepEntry.Buffers)
        (point step : BitVec 64) (time : Binary64.Value) (flag : Bool),
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals inputMessage = some message →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "logger") = some (.pointer none) →
      load heap (p.member "time") = some (.finite time) →
      Storage heap p buffers → ¬ StepEntry.InputsValid point step time → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
          heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3,
          LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩ := by
  letI : CInterface := context.target
  intro program fn tail signature body closed heap p message buffers point step time flag
    defined helper literal kindValue modeCell loggerValue clock stored invalid behavior
  have certified := input_prefix_for_tail (StepErrors.types context) fn tail signature body closed
    heap p buffers point step time flag kindValue
    (by simp [load, modeCell, convert]) clock stored invalid
  exact StaticErrors.prefix_missing_behaviors context program fn _ heap
    (StepEntry.outputHeap heap buffers time) p message inputMessage (some (.integer 4))
    certified defined helper literal
    ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue) behavior

/-- Complete invalid-input rejection for the supplied function under every
checked error context. Function syntax is an obligation of the constructor,
not a hypothesis required from users of these behavior fields. -/
structure InputRejectionContract (fn : Function) : Prop where
  silent : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (logger : Option Address),
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals inputMessage = some message →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    Storage heap p buffers →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    ¬ StepEntry.InputsValid point step time → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
        heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩
  logged : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message category logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals inputMessage = some message →
    program.addresses logger = some name →
    program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    literals "logStatus" = some category →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    Storage heap p buffers →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    ¬ StepEntry.InputsValid point step time → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
        heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated)
        events value after ∧ behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated)
        events value after) ∧ behavior = .wrong [])
  missing : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool),
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals inputMessage = some message →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "logger") = some (.pointer none) →
    load heap (p.member "time") = some (.finite time) →
    Storage heap p buffers → ¬ StepEntry.InputsValid point step time → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
        heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩

theorem input_rejection_contract (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard :: tail)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) :
    InputRejectionContract fn where
  silent := by
    intro literals E context program
    exact context_input_silent_for_tail context program fn tail signature body closed
  logged := by
    intro literals E context program
    exact context_input_logged_for_tail context program fn tail signature body closed
  missing := by
    intro literals E context program
    exact input_missing_context context program fn tail signature body closed

/-- Missing-output rejection precedes all buffer access and numerical checks.
Each field is quantified over arbitrary checked error contexts. -/
structure OutputRejectionContract (fn : Function) : Prop where
  silent : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool) (logger : Option Address),
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals "Missing output pointer" = some message →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    MissingOutput outputs → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag outputs)
        heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩
  logged : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message category logger : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool)
      (environment : Option Address) (name : String) (foreign : CCalls.Events.External E),
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals "Missing output pointer" = some message →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name → literals "logStatus" = some category →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    MissingOutput outputs → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag outputs)
        heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong [])
  missing : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals),
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (outputs : StepEntry.Outputs) (point step : BitVec 64) (flag : Bool),
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals "Missing output pointer" = some message →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "logger") = some (.pointer none) →
    MissingOutput outputs → ∀ behavior,
    (CCalls.Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag outputs)
        heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem output_rejection_contract (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard :: tail)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) :
    OutputRejectionContract fn where
  silent := by
    intro literals E context program heap p message outputs point step flag logger
      defined helper literal kindValue modeCell loggerValue loggingValue missing behavior
    letI : CInterface := context.target
    have certified := outputs_prefix_for_tail (StepErrors.types context) fn tail signature body closed
      heap p point step flag outputs kindValue (by simp [load, modeCell, convert]) missing
    exact StaticErrors.prefix_suppressed_behaviors context program fn _ heap heap p message
      "Missing output pointer" (some (.integer 4)) logger false certified defined helper literal
      modeCell loggerValue loggingValue (Or.inr rfl) behavior
  logged := by
    intro literals E context program heap p message category logger outputs point step flag
      environment name foreign defined helper literal address external prototype categoryBound
      kindValue modeCell loggerValue loggingValue environmentValue missing behavior
    letI : CInterface := context.target
    have certified := outputs_prefix_for_tail (StepErrors.types context) fn tail signature body closed
      heap p point step flag outputs kindValue (by simp [load, modeCell, convert]) missing
    exact StaticErrors.prefix_all_behaviors context program fn _ heap heap p message category logger
      "Missing output pointer" name environment (some (.integer 4)) foreign certified defined helper
      literal address external prototype categoryBound modeCell loggerValue loggingValue environmentValue behavior
  missing := by
    intro literals E context program heap p message outputs point step flag
      defined helper literal kindValue modeCell loggerValue missing behavior
    letI : CInterface := context.target
    have certified := outputs_prefix_for_tail (StepErrors.types context) fn tail signature body closed
      heap p point step flag outputs kindValue (by simp [load, modeCell, convert]) missing
    exact StaticErrors.prefix_missing_behaviors context program fn _ heap heap p message
      "Missing output pointer" (some (.integer 4)) certified defined helper literal
      modeCell loggerValue behavior

theorem scalar_input_contract (model : Solve.FMI3Model source) :
    InputRejectionContract (Runtime.function model StepEntry.signature) := by
  apply input_rejection_contract (Runtime.function model StepEntry.signature)
    (Runtime.doStep.drop 9) rfl _
    (BodyEmbedding.body_closed model StepEntry.signature)
  exact StepEntry.body model

theorem scalar_output_contract (model : Solve.FMI3Model source) :
    OutputRejectionContract (Runtime.function model StepEntry.signature) := by
  apply output_rejection_contract (Runtime.function model StepEntry.signature)
    (Runtime.doStep.drop 9) rfl _ (BodyEmbedding.body_closed model StepEntry.signature)
  exact StepEntry.body model

open CCalls in
theorem ready_prefix_for_tail {E : Type} (context : ErrorContext literals)
    (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++ StepEntry.inputGuard :: tail)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool),
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → Storage heap p buffers →
      StepEntry.InputsValid point step time →
      ∃ types, Transition.Events.Prefix (Events.machine program)
        (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) []
        (.body (.running tail
          (StepEntry.locals (StepEntry.parameters (some p) point step flag buffers.outputs) p)
          types (StepEntry.outputHeap heap buffers time)) "fmi3Status" .done) := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag defined kindValue modeValue clock stored valid
  let env := StepEntry.parameters (some p) point step flag buffers.outputs
  let later := StepEntry.locals env p
  obtain ⟨old, last⟩ := stored.last
  have ran := StepEntry.prefix_run_suffix (StepErrors.types context) env heap p buffers point step time old
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, StepEntry.Buffers.outputs, CBody.bind])
    clock stored.event stored.terminate stored.early last stored.outsideEvent
    stored.outsideTerminate stored.outsideEarly stored.outsideLast tail
  have executed : run 9 (.running fn.body env heap) =
      some (.running tail later (StepEntry.outputHeap heap buffers time)) := by
    simpa only [body, List.append_assoc, List.singleton_append, valid, ↓reduceIte,
      List.nil_append] using ran
  have parameters : CCalls.parameters fn.signature.parameters
      (StepEntry.arguments (some p) point step flag buffers.outputs) = some env := by
    rw [signature]
    exact StepEntry.parameters_bound (StepErrors.types context) _ _ _ _ _
  obtain ⟨types, entered⟩ := Events.body_prefix_reaches program fn _ env later heap
    (StepEntry.outputHeap heap buffers time) tail .done 9 defined parameters closed executed
  have status : fn.signature.result = "fmi3Status" := by rw [signature]; rfl
  rw [status] at entered
  exact ⟨types, Events.internal_path program entered⟩

/-- Initializing the four writable step outputs preserves every existing
read-only cell, including literals. Boolean outputs may still alias. -/
theorem Storage.output_readonly
    (stored : StepArguments.Storage heap p buffers) (time : Binary64.Value) :
    CReadOnly.Preserves heap (StepEntry.outputHeap heap buffers time) := by
  intro query cell found readonly
  have separate (address : Address) (type : CType) (old : Option Value)
      (writable : heap address = some ⟨type, true, old⟩) : query ≠ address := by
    intro same
    subst address
    rw [writable] at found
    cases found
    cases readonly
  obtain ⟨eventOld, event⟩ := stored.event
  obtain ⟨terminateOld, terminate⟩ := stored.terminate
  obtain ⟨earlyOld, early⟩ := stored.early
  obtain ⟨lastOld, last⟩ := stored.last
  exact (StepEntry.output_frame heap buffers time query
    (separate _ _ _ event) (separate _ _ _ terminate)
    (separate _ _ _ early) (separate _ _ _ last)).trans found

/-- Error callback entry includes the output initialization followed by the
required terminated-mode write. Both preserve pre-existing immutable storage. -/
theorem Storage.error_readonly
    (stored : StepArguments.Storage heap p buffers) (time : Binary64.Value)
    (old : Option Value)
    (mode : heap (p.member "mode") = some ⟨.int32, true, old⟩) :
    CReadOnly.Preserves heap
      (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) :=
  (stored.output_readonly time).trans (LifecycleBodies.writeMode_readonly _ p .terminated old
    ((stored.instance_frame time (p.member "mode") rfl).trans mode))

/-- A pool-derived literal survives at discard callback entry. This frame is
derived from writable output storage, not a separate successful-run premise. -/
theorem Storage.literal_at_output
    {reserved : List String} (pool : CLiteral.Pool reserved)
    (before : Heap) (firstBlock : Nat) (signed : Bool)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (stored : StepArguments.Storage heap p buffers) (time : Binary64.Value)
    (text : String) (address : Address)
    (bound : pool.addresses firstBlock text = some address) :
    CLiteral.StoredContents signed (pool.install before firstBlock signed)
      (StepEntry.outputHeap heap buffers time) address text :=
  CLiteral.stored_contents pool before firstBlock signed _
    (frame.trans (stored.output_readonly time)) text address bound

/-- A pool-derived literal survives at error callback entry. No frame is
asserted after the external callback. -/
theorem Storage.literal_at_error
    {reserved : List String} (pool : CLiteral.Pool reserved)
    (before : Heap) (firstBlock : Nat) (signed : Bool)
    (frame : CReadOnly.Preserves (pool.install before firstBlock signed) heap)
    (stored : StepArguments.Storage heap p buffers) (time : Binary64.Value)
    (old : Option Value)
    (mode : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (text : String) (address : Address)
    (bound : pool.addresses firstBlock text = some address) :
    CLiteral.StoredContents signed (pool.install before firstBlock signed)
      (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) address text :=
  CLiteral.stored_contents pool before firstBlock signed _
    (frame.trans (stored.error_readonly time old mode)) text address bound


end Rumoca.FMI3.StepArguments
end
