import RumocaFMI3.StepErrors

/-! Complete public CS argument errors, including the exact output writes
before numerical rejection. Rounding, stop and discard paths remain separate. -/
noncomputable section
namespace Rumoca.FMI3.StepArguments
open CTree CMemory CBody
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def MissingOutput (outputs : StepEntry.Outputs) : Prop :=
  outputs.event = none ∨ outputs.terminate = none ∨ outputs.early = none ∨ outputs.last = none

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
  let env := StepEntry.parameters (some p) point step flag outputs
  let later := StepEntry.locals env p
  let rest := StepEntry.outputCode.drop 1 ++ StepEntry.inputGuard :: Runtime.doStep.drop 9
  have entered := StepEntry.lifecycle_run (StepErrors.types context) env heap p .cs .step
    (StepEntry.outputCode ++ StepEntry.inputGuard :: Runtime.doStep.drop 9)
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
  simp only [allowed, permittedModes] at entered
  have checked : run 1 (.running (StepEntry.outputCode ++ StepEntry.inputGuard :: Runtime.doStep.drop 9)
      later heap) = some (.running (Runtime.fail "Missing output pointer" :: rest) later heap) := by
    rcases outputs with ⟨event, terminate, early, last⟩
    cases event <;> cases terminate <;> cases early <;> cases last <;>
      simp_all [MissingOutput, run, next, StepEntry.outputCode, Runtime.pointerCheck,
        Runtime.reject, Runtime.branch, Runtime.any, Runtime.negate, Runtime.v, Runtime.n,
        Runtime.either, eval, resolve, later, env, StepEntry.locals, StepEntry.parameters,
        StepEntry.bindings, CBody.bind, Value.truth, boolean, rest]
  refine ⟨rfl, BodyEmbedding.body_closed model StepEntry.signature,
    env, later, rest, 4, StepEntry.parameters_bound (StepErrors.types context) _ _ _ _ _, ?_, ?_, ?_⟩
  · change run 4 (.running (Runtime.body model StepEntry.signature) env heap) = _
    rw [StepEntry.body, List.append_assoc, show 4 = 3 + 1 from rfl, run_add, entered]
    exact checked
  · simp [later, StepEntry.locals, env, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [later, StepEntry.locals, CBody.bind, resolve]

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
  refine ⟨rfl, BodyEmbedding.body_closed model StepEntry.signature, env, later,
    Runtime.doStep.drop 9, 9, StepEntry.parameters_bound (StepErrors.types context) _ _ _ _ _, ?_, ?_, ?_⟩
  · simpa only [StepEntry.inputDestination, invalid, ↓reduceIte, List.singleton_append] using ran
  · simp [later, StepEntry.locals, env, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [later, StepEntry.locals, CBody.bind, resolve]

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

end Rumoca.FMI3.StepArguments
end
