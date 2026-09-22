import RumocaFMI3.StepArguments

/-! Complete public CS rounding and stop-limit errors. These proofs compose
ordinary library observations with output writes and the actual error helper;
native floating-environment correspondence and discard remain separate. -/
noncomputable section
namespace Rumoca.FMI3.StepFailures
open CTree CMemory CBody CCalls
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def roundingMessage := "Round-to-nearest arithmetic is required"
def stopMessage := "Step exceeds stopTime"

def entryLocals (p : Address) (buffers : StepEntry.Buffers)
    (point step : BitVec 64) (flag : Bool) : Locals :=
  StepEntry.locals (StepEntry.parameters (some p) point step flag buffers.outputs) p

def roundingLocals (p : Address) (buffers : StepEntry.Buffers)
    (point step : BitVec 64) (flag : Bool) (observed : Int) : Locals :=
  bind (entryLocals p buffers point step flag) "rounding" (.integer observed)

def roundingRest := Runtime.stepClock ++ Runtime.stepGrid ++ StepAdvance.code

def roundingDestination (header : CFenv.Header) (observed : Int) :=
  (if observed = header.nearest then [] else [Runtime.fail roundingMessage]) ++ roundingRest

/-- Public admission and the ordinary rounding observation form one determined
prefix. Output initialization precedes it; clock arithmetic follows it. -/
theorem rounding_entry (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point step time →
      ∃ types, Transition.Events.Prefix (Events.machine program)
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) []
        (.body (.running (roundingDestination header observed)
          (roundingLocals p buffers point step flag observed) types (StepEntry.outputHeap heap buffers time))
          "fmi3Status" .done) := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag observed range integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid
  obtain ⟨types, entered⟩ := StepArguments.ready_prefix context model program heap p buffers point step time flag
    defined kindValue modeValue clock stored valid
  have checked := StepGuards.rounding_path program header (entryLocals p buffers point step flag) types
    (StepEntry.outputHeap heap buffers time) observed range roundingRest "fmi3Status" .done integer
    (by simp [entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    ordinary macroBound rounding
  rw [StepGuards.actual_sections, List.append_assoc, List.append_assoc] at entered
  have path := entered.trans checked
  exact ⟨_, by simpa only [roundingDestination, roundingMessage, roundingLocals, List.nil_append] using path⟩

theorem rounding_prefix (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point step time → observed ≠ header.nearest →
      StaticErrors.FailurePath program
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) p roundingMessage := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag observed range integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid rejected
  obtain ⟨types, path⟩ := rounding_entry context model header program heap p buffers point step time flag
    observed range integer ordinary macroBound rounding defined kindValue modeValue clock stored valid
  refine ⟨roundingLocals p buffers point step flag observed, types, roundingRest, ?_, ?_, ?_⟩
  · simpa only [roundingDestination, rejected, ↓reduceIte, List.singleton_append] using path
  · simp [roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [roundingLocals, entryLocals, StepEntry.locals, CBody.bind, resolve]

/-- A stop-limit failure follows the rounded sum, including its overflow cases.
It precedes progress and unit-grid rejection and does not invoke the solver. -/
theorem stop_prefix (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point : BitVec 64) (step time : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      StepGuards.AboveStop (Binary64.addResult time step) stop →
      StaticErrors.FailurePath program
        (.calling StepEntry.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) p stopMessage := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag stop integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid enabled limit exceeds
  obtain ⟨types, entered⟩ := rounding_entry context model header program heap p buffers point
    (Binary64.toBits step).val time flag header.nearest _ integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid
  let env := roundingLocals p buffers point (Binary64.toBits step).val flag header.nearest
  have double : CInterface.types "double" = some .float64 := by rw [← context.types]; rfl
  have checked := StepGuards.clock_path program env types (StepEntry.outputHeap heap buffers time)
    p time step stop (Runtime.stepGrid ++ StepAdvance.code) "fmi3Status" .done double
    (by simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, roundingLocals, entryLocals, StepEntry.locals, CBody.bind])
    (by simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings,
      CBody.bind, Value.finite])
    ((stored.load_field time "time").trans clock) ((stored.load_field time "stopDefined").trans enabled)
    (fun value chosen => (stored.load_field time "stop").trans (limit value chosen))
  simp only [roundingDestination, ↓reduceIte, List.nil_append] at entered
  have path := entered.trans checked
  refine ⟨bind env "next" (.float64 (Binary64.addResult time step).encode),
    CLoops.bindType types "next" .float64,
    Runtime.stepClock.drop 2 ++ (Runtime.stepGrid ++ StepAdvance.code), ?_, ?_, ?_⟩
  · simpa only [StepGuards.clockDestination, exceeds, ↓reduceIte, stopMessage, List.nil_append] using path
  · simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [env, roundingLocals, entryLocals, StepEntry.locals, CBody.bind, resolve]

theorem rounding_suppressed {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32) (logger : Option Address) (logging : Bool),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals roundingMessage = some message →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point step time → observed ≠ header.nearest →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩ := by
  letI : CInterface := context.target
  intro program heap p message buffers point step time flag observed range integer logger logging
    ordinary macroBound rounding defined helper literal kindValue modeCell clock stored valid rejected
    loggerValue loggingValue suppressed behavior
  have path := rounding_prefix context model header program heap p buffers point step time flag observed range
    integer ordinary macroBound rounding defined kindValue (by simp [load, modeCell, convert]) clock stored valid rejected
  exact StaticErrors.path_suppressed_behaviors context program _ (StepEntry.outputHeap heap buffers time)
    p message roundingMessage _ logger logging path helper literal
    ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue) ((stored.load_field time "logging").trans loggingValue)
    suppressed behavior

theorem rounding_logged {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message category logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : Events.External E),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals roundingMessage = some message → literals "logStatus" = some category →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point step time → observed ≠ header.nearest →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧
        behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program heap p message category logger buffers point step time flag observed range integer
    environment name foreign ordinary macroBound rounding defined helper literal categoryBound address external
    prototype kindValue modeCell clock stored valid rejected loggerValue loggingValue environmentValue behavior
  have path := rounding_prefix context model header program heap p buffers point step time flag observed range
    integer ordinary macroBound rounding defined kindValue (by simp [load, modeCell, convert]) clock stored valid rejected
  exact StaticErrors.path_all_behaviors context program _ (StepEntry.outputHeap heap buffers time)
    p message category logger roundingMessage name environment _ foreign path helper literal address external
    prototype categoryBound ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue) ((stored.load_field time "logging").trans loggingValue)
    ((stored.load_field time "environment").trans environmentValue) behavior

theorem stop_suppressed {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message : Address) (buffers : StepEntry.Buffers)
      (point : BitVec 64) (step time : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32) (logger : Option Address) (logging : Bool),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals stopMessage = some message →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      StepGuards.AboveStop (Binary64.addResult time step) stop →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling StepEntry.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩ := by
  letI : CInterface := context.target
  intro program heap p message buffers point step time flag stop integer logger logging
    ordinary macroBound rounding defined helper literal kindValue modeCell clock stored valid enabled limit exceeds
    loggerValue loggingValue suppressed behavior
  have path := stop_prefix context model header program heap p buffers point step time flag stop integer
    ordinary macroBound rounding defined kindValue (by simp [load, modeCell, convert]) clock stored valid enabled limit exceeds
  exact StaticErrors.path_suppressed_behaviors context program _ (StepEntry.outputHeap heap buffers time)
    p message stopMessage _ logger logging path helper literal
    ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue) ((stored.load_field time "logging").trans loggingValue)
    suppressed behavior

theorem stop_logged {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message category logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : Events.External E),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals stopMessage = some message → literals "logStatus" = some category →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      StepGuards.AboveStop (Binary64.addResult time step) stop →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling StepEntry.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated) events value after) ∧
        behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program heap p message category logger buffers point step time flag stop integer environment name foreign
    ordinary macroBound rounding defined helper literal categoryBound address external prototype kindValue modeCell
    clock stored valid enabled limit exceeds loggerValue loggingValue environmentValue behavior
  have path := stop_prefix context model header program heap p buffers point step time flag stop integer
    ordinary macroBound rounding defined kindValue (by simp [load, modeCell, convert]) clock stored valid enabled limit exceeds
  exact StaticErrors.path_all_behaviors context program _ (StepEntry.outputHeap heap buffers time)
    p message category logger stopMessage name environment _ foreign path helper literal address external
    prototype categoryBound ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
    ((stored.load_field time "logger").trans loggerValue) ((stored.load_field time "logging").trans loggingValue)
    ((stored.load_field time "environment").trans environmentValue) behavior

/-- Output initialization and the ordinary rounding observation reach the
selected guard continuation, for an arbitrary actual function and later tail. -/
theorem rounding_entry_for_tail {E : Type} (context : ErrorContext literals)
    (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: (Runtime.stepRounding ++ tail))
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point step time →
      ∃ types, Transition.Events.Prefix (Events.machine program)
        (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done) []
        (.body (.running ((if observed = header.nearest then [] else [Runtime.fail roundingMessage]) ++ tail)
          (roundingLocals p buffers point step flag observed) types (StepEntry.outputHeap heap buffers time))
          "fmi3Status" .done) := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag observed range integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid
  obtain ⟨types, entered⟩ := StepArguments.ready_prefix_for_tail context fn
    (Runtime.stepRounding ++ tail) signature body closed program heap p buffers point step time flag
    defined kindValue modeValue clock stored valid
  have checked := StepGuards.rounding_path program header (entryLocals p buffers point step flag) types
    (StepEntry.outputHeap heap buffers time) observed range tail "fmi3Status" .done integer
    (by simp [entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    ordinary macroBound rounding
  have path := entered.trans checked
  exact ⟨_, by simpa only [roundingMessage, roundingLocals, List.nil_append] using path⟩

/-- A rejected ordinary rounding observation reaches the actual failure call
without requiring or executing any numerical solver state. -/
theorem rounding_prefix_for_tail {E : Type} (context : ErrorContext literals)
    (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: (Runtime.stepRounding ++ tail))
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point step : BitVec 64) (time : Binary64.Value) (flag : Bool)
      (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point step time → observed ≠ header.nearest →
      StaticErrors.FailurePath program
        (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) p roundingMessage := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag observed range integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid rejected
  obtain ⟨types, path⟩ := rounding_entry_for_tail context fn tail signature body closed header
    program heap p buffers point step time flag observed range integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid
  refine ⟨roundingLocals p buffers point step flag observed, types, tail, ?_, ?_, ?_⟩
  · simpa only [rejected, ↓reduceIte, List.singleton_append] using path
  · simp [roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [roundingLocals, entryLocals, StepEntry.locals, CBody.bind, resolve]

/-- Actual public entry, output initialization and rounding observation reach
the rounded clock's guard destination. Overflow is not excluded. -/
theorem clock_entry_for_tail {E : Type} (context : ErrorContext literals)
    (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: (Runtime.stepRounding ++ Runtime.stepClock ++ tail))
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point : BitVec 64) (step time : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ∃ types, Transition.Events.Prefix (Events.machine program)
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) []
        (.body (.running (StepGuards.clockDestination time (Binary64.addResult time step) stop tail)
          (CBody.bind (roundingLocals p buffers point (Binary64.toBits step).val flag header.nearest)
            "next" (.float64 (Binary64.addResult time step).encode))
          (CLoops.bindType types "next" .float64) (StepEntry.outputHeap heap buffers time))
          "fmi3Status" .done) := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag stop integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid enabled limit
  obtain ⟨types, entered⟩ := rounding_entry_for_tail context fn (Runtime.stepClock ++ tail)
    signature (by simpa only [List.append_assoc] using body) closed header program heap p buffers
    point (Binary64.toBits step).val time flag header.nearest _ integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid
  let env := roundingLocals p buffers point (Binary64.toBits step).val flag header.nearest
  have double : CInterface.types "double" = some .float64 := by rw [← context.types]; rfl
  have checked := StepGuards.clock_path program env types (StepEntry.outputHeap heap buffers time)
    p time step stop tail "fmi3Status" .done double
    (by simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, roundingLocals, entryLocals, StepEntry.locals, CBody.bind])
    (by simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings,
      CBody.bind, Value.finite])
    ((stored.load_field time "time").trans clock) ((stored.load_field time "stopDefined").trans enabled)
    (fun value chosen => (stored.load_field time "stop").trans (limit value chosen))
  simp only [↓reduceIte, List.nil_append] at entered
  exact ⟨types, by simpa only [List.nil_append] using entered.trans checked⟩

/-- Stop rejection precedes progress and unit-grid checks, for every numerical
tail. The rounded clock may be nonfinite. -/
theorem stop_prefix_for_tail {E : Type} (context : ErrorContext literals)
    (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: (Runtime.stepRounding ++ Runtime.stepClock ++ tail))
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point : BitVec 64) (step time : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      StepGuards.AboveStop (Binary64.addResult time step) stop →
      StaticErrors.FailurePath program
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) p stopMessage := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag stop integer ordinary macroBound rounding
    defined kindValue modeValue clock stored valid enabled limit exceeds
  obtain ⟨types, path⟩ := clock_entry_for_tail context fn tail signature body closed header
    program heap p buffers point step time flag stop integer ordinary macroBound rounding defined
    kindValue modeValue clock stored valid enabled limit
  refine ⟨CBody.bind (roundingLocals p buffers point (Binary64.toBits step).val flag header.nearest)
    "next" (.float64 (Binary64.addResult time step).encode), CLoops.bindType types "next" .float64,
    Runtime.stepClock.drop 2 ++ tail, ?_, ?_, ?_⟩
  · simpa only [StepGuards.clockDestination, exceeds, ↓reduceIte, stopMessage] using path
  · simp [roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [roundingLocals, entryLocals, StepEntry.locals, CBody.bind, resolve]

/-- Complete rejection of an observed rounding mode other than the supplied
header's nearest mode. Syntax and the execution prefix are constructor obligations. -/
structure RoundingRejectionContract (fn : Function) : Prop where
  silent : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals)
    (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32) (logger : Option Address),
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals roundingMessage = some message →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) → ∀ behavior,
    (Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
        heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩
  logged : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals)
    (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message category logger : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : Events.External E),
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals roundingMessage = some message →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name → literals "logStatus" = some category →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
    (Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
        heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated)
        events value after ∧ behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated)
        events value after) ∧ behavior = .wrong [])
  missing : ∀ (literals : CLiteralAddresses) {E : Type} (context : ErrorContext literals)
    (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message : Address)
      (buffers : StepEntry.Buffers) (point step : BitVec 64) (time : Binary64.Value)
      (flag : Bool) (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
      (integer : context.target.types "int" = some .int32),
    context.target.constants "fegetround" = none →
    context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
    program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range) →
    program.internal.definitions fn.signature.name = some (.tree fn) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    literals roundingMessage = some message →
    load heap (p.member "kind") = some (.integer 1) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
    load heap (p.member "time") = some (.finite time) →
    StepArguments.Storage heap p buffers → StepEntry.InputsValid point step time →
    observed ≠ header.nearest →
    load heap (p.member "logger") = some (.pointer none) → ∀ behavior,
    (Events.machine program).Behaves
      (.calling fn.signature.name (StepEntry.arguments (some p) point step flag buffers.outputs)
        heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩

theorem rounding_rejection_contract (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: (Runtime.stepRounding ++ tail))
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) :
    RoundingRejectionContract fn where
  silent := by
    intro literals E context header program heap p message buffers point step time flag observed range
      integer logger ordinary macroBound rounding defined helper literal kindValue modeCell clock stored
      valid rejected loggerValue loggingValue behavior
    letI : CInterface := context.target
    have path := rounding_prefix_for_tail context fn tail signature body closed header
      program heap p buffers point step time flag observed range integer ordinary macroBound rounding
      defined kindValue (by simp [load, modeCell, convert]) clock stored valid rejected
    exact StaticErrors.path_suppressed_behaviors context program _
      (StepEntry.outputHeap heap buffers time) p message roundingMessage (some (.integer 4)) logger false
      path helper literal ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
      ((stored.load_field time "logger").trans loggerValue)
      ((stored.load_field time "logging").trans loggingValue) (Or.inr rfl) behavior
  logged := by
    intro literals E context header program heap p message category logger buffers point step time flag
      observed range integer environment name foreign ordinary macroBound rounding defined helper literal
      address external prototype categoryBound kindValue modeCell clock stored valid rejected
      loggerValue loggingValue environmentValue behavior
    letI : CInterface := context.target
    have path := rounding_prefix_for_tail context fn tail signature body closed header
      program heap p buffers point step time flag observed range integer ordinary macroBound rounding
      defined kindValue (by simp [load, modeCell, convert]) clock stored valid rejected
    exact StaticErrors.path_all_behaviors context program _
      (StepEntry.outputHeap heap buffers time) p message category logger roundingMessage name environment
      (some (.integer 4)) foreign path helper literal address external prototype categoryBound
      ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
      ((stored.load_field time "logger").trans loggerValue)
      ((stored.load_field time "logging").trans loggingValue)
      ((stored.load_field time "environment").trans environmentValue) behavior
  missing := by
    intro literals E context header program heap p message buffers point step time flag observed range
      integer ordinary macroBound rounding defined helper literal kindValue modeCell clock stored
      valid rejected loggerValue behavior
    letI : CInterface := context.target
    have path := rounding_prefix_for_tail context fn tail signature body closed header
      program heap p buffers point step time flag observed range integer ordinary macroBound rounding
      defined kindValue (by simp [load, modeCell, convert]) clock stored valid rejected
    exact StaticErrors.path_missing_behaviors context program _
      (StepEntry.outputHeap heap buffers time) p message roundingMessage (some (.integer 4))
      path helper literal ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
      ((stored.load_field time "logger").trans loggerValue) behavior

/-- Stop-limit rejection under every checked error context and rounding header.
The silent field retains the scalar suppressed-case premises verbatim, including
both logger-null and logging-disabled alternatives. The missing field separately
removes any logging-flag or callback-environment/category requirement.
-/
structure StopRejectionContract (fn : Function) : Prop where
  silent : ∀ (literals : CLiteralAddresses) {E : Type}
      (context : ErrorContext literals) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32) (logger : Option Address) (logging : Bool),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals stopMessage = some message →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      StepGuards.AboveStop (Binary64.addResult time step) stop →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs)
          heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩
  logged : ∀ (literals : CLiteralAddresses) {E : Type}
      (context : ErrorContext literals) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message category logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (environment : Option Address) (name : String) (foreign : Events.External E),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals stopMessage = some message → literals "logStatus" = some category →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      StepGuards.AboveStop (Binary64.addResult time step) stop →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs)
          heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated)
        events value after ∧ behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated)
        events value after) ∧ behavior = .wrong [])
  missing : ∀ (literals : CLiteralAddresses) {E : Type}
      (context : ErrorContext literals) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p message : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals stopMessage = some message →
      load heap (p.member "kind") = some (.integer 1) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer 4)⟩ →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      StepGuards.AboveStop (Binary64.addResult time step) stop →
      load heap (p.member "logger") = some (.pointer none) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs)
          heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3,
        LifecycleBodies.writeMode (StepEntry.outputHeap heap buffers time) p .terminated⟩

/-- Derive the failure path from actual syntax, then compose the appropriate
helper behavior. No behavior field assumes syntax or successful execution. -/
theorem stop_rejection_contract (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: (Runtime.stepRounding ++ Runtime.stepClock ++ tail))
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) :
    StopRejectionContract fn where
  silent := by
    intro literals E context header program heap p message buffers point step time flag stop
      integer logger logging ordinary macroBound rounding defined helper literal kindValue modeCell
      clock stored valid enabled limit exceeds loggerValue loggingValue suppressed behavior
    letI : CInterface := context.target
    have path := stop_prefix_for_tail context fn tail signature body closed header program heap p
      buffers point step time flag stop integer ordinary macroBound rounding defined kindValue
      (by simp [load, modeCell, convert]) clock stored valid enabled limit exceeds
    exact StaticErrors.path_suppressed_behaviors context program _ (StepEntry.outputHeap heap buffers time)
      p message stopMessage _ logger logging path helper literal
      ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
      ((stored.load_field time "logger").trans loggerValue)
      ((stored.load_field time "logging").trans loggingValue) suppressed behavior
  logged := by
    intro literals E context header program heap p message category logger buffers point step time
      flag stop integer environment name foreign ordinary macroBound rounding defined helper literal
      categoryBound address external prototype kindValue modeCell clock stored valid enabled limit
      exceeds loggerValue loggingValue environmentValue behavior
    letI : CInterface := context.target
    have path := stop_prefix_for_tail context fn tail signature body closed header program heap p
      buffers point step time flag stop integer ordinary macroBound rounding defined kindValue
      (by simp [load, modeCell, convert]) clock stored valid enabled limit exceeds
    exact StaticErrors.path_all_behaviors context program _ (StepEntry.outputHeap heap buffers time)
      p message category logger stopMessage name environment _ foreign path helper literal address external
      prototype categoryBound ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
      ((stored.load_field time "logger").trans loggerValue)
      ((stored.load_field time "logging").trans loggingValue)
      ((stored.load_field time "environment").trans environmentValue) behavior
  missing := by
    intro literals E context header program heap p message buffers point step time flag stop integer
      ordinary macroBound rounding defined helper literal kindValue modeCell clock stored valid
      enabled limit exceeds loggerValue behavior
    letI : CInterface := context.target
    have path := stop_prefix_for_tail context fn tail signature body closed header program heap p
      buffers point step time flag stop integer ordinary macroBound rounding defined kindValue
      (by simp [load, modeCell, convert]) clock stored valid enabled limit exceeds
    exact StaticErrors.path_missing_behaviors context program _ (StepEntry.outputHeap heap buffers time)
      p message stopMessage _ path helper literal
      ((stored.instance_frame time (p.member "mode") rfl).trans modeCell)
      ((stored.load_field time "logger").trans loggerValue) behavior

end Rumoca.FMI3.StepFailures
end
