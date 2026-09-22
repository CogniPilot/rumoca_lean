import RumocaFMI3.StepFailures

/-! Complete public CS discard calls after valid input and rounding admission.
The stop guard precedes discard; output initialization preserves all instance
fields. Callback execution retains every represented outcome. -/
noncomputable section
namespace Rumoca.FMI3.StepDiscard
open CTree CMemory CBody CCalls
set_option maxRecDepth 10000
-- Exact normalization of binary64 overflow bounds (also used by StepAdmission).
set_option exponentiation.threshold 4096
set_option maxHeartbeats 1000000

def message := "Step cannot be completed on the unit internal time grid"

def arguments (environment : Option Address) (category text : Address) : List Value :=
  [.pointer environment, .integer 2, .pointer (some category), .pointer (some text)]

def continuation (env : Locals) (types : CLoops.Types) (rest : List Stmt) (stack : Typed.Continuation) :=
  Typed.Continuation.caller .discard (Runtime.ret (Runtime.v "fmi3Discard") :: rest) env types "fmi3Status" stack

def logCall := Stmt.eval (.call (Runtime.field "logger")
  [Runtime.field "environment", Runtime.v "fmi3Discard", .str "logStatus", .str message])

theorem arguments_converted (context : ErrorContext literals) (name : String)
    (environment : Option Address) (category text : Address) :
    @Events.convertedArguments context.target (Logging.signature name).parameters
      (arguments environment category text) = some (arguments environment category text) := by
  simp [Events.convertedArguments, Logging.signature, arguments, CCalls.parameters, CBody.bind,
    CBody.cast, ← context.types, CCalls.parameterType, convert]

theorem resume_reaches (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (stack : Typed.Continuation) (value : Value) (heap : Heap),
      resolve env "fmi3Discard" = some (.integer 2) →
      Transition.Reaches (fun s t => Events.internalNext program s = some t)
        (.returning value heap (continuation env types rest stack))
        (.returning (.integer 2) heap stack) := by
  letI : CInterface := context.target
  intro program env types rest stack value heap statusValue
  have cast : CCalls.returnCast "fmi3Status" (.integer 2) = some (.integer 2) := by
    simp [CCalls.returnCast, CBody.cast, ← context.types, convert]
  refine .next (t := .body (.running (Runtime.ret (Runtime.v "fmi3Discard") :: rest) env types heap)
    "fmi3Status" stack) (by rfl) ?_
  refine .next (t := .body (.returned ⟨.integer 2, heap⟩) "fmi3Status" stack) ?_ ?_
  · simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, Runtime.ret, Runtime.v,
      CBody.eval, CBody.evalWith, statusValue]
  · exact .next (by simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, cast]) (.refl _)

theorem suppressed_reaches (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (heap : Heap) (p : Address) (logger : Option Address) (logging : Bool) (stack : Typed.Continuation),
      resolve env "m" = some (.pointer (some p)) →
      resolve env "fmi3Discard" = some (.integer 2) →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) →
      Transition.Reaches (fun s t => Events.internalNext program s = some t)
        (.body (.running (Runtime.stepDiscard ++ rest) env types heap) "fmi3Status" stack)
        (.returning (.integer 2) heap stack) := by
  letI : CInterface := context.target
  intro program env types rest heap p logger logging stack instanceValue statusValue loggerValue loggingValue suppressed
  have disabled : eval env heap (Runtime.both
      (Runtime.nev (Runtime.field "logger") Expr.nullPointer) (Runtime.field "logging")) =
      some (.integer 0) := by
    change eval env heap (.bin .and (.bin .ne (Runtime.field "logger") Expr.nullPointer)
      (Runtime.field "logging")) = _
    rw [CNull.and_unequal_null_eval _ _ env heap logger
      (by simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address, loggerValue])
      (by change context.target.types "void *" = some .pointer; rw [← context.types]; rfl)]
    rcases suppressed with rfl | rfl
    · simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address, loggerValue, Value.truth, boolean]
    · cases logger <;> simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address,
        loggerValue, loggingValue, Value.truth, boolean]
  simp only [Runtime.both, Runtime.nev] at disabled
  have cast : CCalls.returnCast "fmi3Status" (.integer 2) = some (.integer 2) := by
    simp [CCalls.returnCast, CBody.cast, ← context.types, convert]
  refine .next (t := .body (.running (Runtime.ret (Runtime.v "fmi3Discard") :: rest) env types heap)
    "fmi3Status" stack) ?_ ?_
  · apply Events.body_step
    simp [Runtime.stepDiscard, Runtime.log, Runtime.branch, Runtime.both, Runtime.nev,
      CLoops.next, CLoops.nextWith, CLoops.noDeclarations, CLoops.evalWith, CBody.legacyExpressions, disabled, Value.truth]
  · refine .next (t := .body (.returned ⟨.integer 2, heap⟩) "fmi3Status" stack) ?_ ?_
    · apply Events.body_step
      simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, Runtime.ret, Runtime.v, CBody.eval, CBody.evalWith, statusValue]
    · exact .next (by simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, cast]) (.refl _)

theorem dispatch_reaches (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (heap : Heap) (p text category logger : Address) (environment : Option Address)
      (name : String) (stack : Typed.Continuation),
      resolve env "m" = some (.pointer (some p)) →
      resolve env "fmi3Discard" = some (.integer 2) →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      program.addresses logger = some name → literals "logStatus" = some category →
      literals message = some text →
      Transition.Reaches (fun s t => Events.internalNext program s = some t)
        (.body (.running (Runtime.stepDiscard ++ rest) env types heap) "fmi3Status" stack)
        (.calling name (arguments environment category text) heap (continuation env types rest stack)) := by
  letI : CInterface := context.target
  intro program env types rest heap p text category logger environment name stack instanceValue statusValue
    loggerValue loggingValue environmentValue address categoryLiteral textLiteral
  have categoryBound : CInterface.literals "logStatus" = some category := context.bytes ▸ categoryLiteral
  have textBound : CInterface.literals message = some text := context.bytes ▸ textLiteral
  have enabled : eval env heap (Runtime.both
      (Runtime.nev (Runtime.field "logger") Expr.nullPointer) (Runtime.field "logging")) =
      some (.integer 1) := by
    change eval env heap (.bin .and (.bin .ne (Runtime.field "logger") Expr.nullPointer)
      (Runtime.field "logging")) = _
    rw [CNull.and_unequal_null_eval _ _ env heap (some logger)
      (by simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address, loggerValue])
      (by change context.target.types "void *" = some .pointer; rw [← context.types]; rfl)]
    simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address,
      loggerValue, loggingValue, Value.truth, boolean]
  simp only [Runtime.both, Runtime.nev] at enabled
  have resolved : Events.resolve program env heap (Runtime.field "logger") = some name := by
    simp [Events.resolve, Events.resolveWith, CCalls.Indirect.resolveWith, CBody.legacyExpressions, Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt,
      instanceValue, Value.address, loggerValue, CCalls.Indirect.valueTarget, address]
  have values : CCalls.arguments env heap
      [Runtime.field "environment", Runtime.v "fmi3Discard", .str "logStatus", .str message] =
      some (arguments environment category text) := by
    simp [CCalls.arguments, CCalls.argumentsWith, CBody.legacyExpressions, Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, statusValue,
      Value.address, environmentValue, categoryBound, textBound, arguments, argumentsWith, CBody.legacyExpressions]
  let tail := Runtime.ret (Runtime.v "fmi3Discard") :: rest
  have blocked : CLoops.next (.running (logCall :: tail) env types heap) = none := by
    simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, logCall, Runtime.field, Runtime.v, CBody.eval, CBody.evalWith]
  refine .next (t := .body (.running (logCall :: tail) env types heap) "fmi3Status" stack) ?_ ?_
  · apply Events.body_step
    simp [Runtime.stepDiscard, Runtime.log, Runtime.branch, Runtime.both, Runtime.nev, CLoops.noDeclarations, CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, enabled,
      Value.truth, logCall, tail, message]
  · refine .next ?_ (.refl _)
    simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, blocked]
    simp [Events.enterCallWith, logCall, CCalls.Indirect.operand, resolved, values, continuation, tail]

theorem suppressed_behaviors (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (heap : Heap) (p : Address) (logger : Option Address) (logging : Bool),
      resolve env "m" = some (.pointer (some p)) →
      resolve env "fmi3Discard" = some (.integer 2) →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves
        (.body (.running (Runtime.stepDiscard ++ rest) env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates [] ⟨.integer 2, heap⟩ := by
  letI : CInterface := context.target
  intro program env types rest heap p logger logging instanceValue statusValue loggerValue loggingValue suppressed behavior
  exact (Events.internal_prefix program
    (suppressed_reaches context program env types rest heap p logger logging .done
      instanceValue statusValue loggerValue loggingValue suppressed)
    (Events.return_forced program (.integer 2) heap)).behaviors behavior

theorem all_behaviors (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (heap : Heap) (p text category logger : Address) (environment : Option Address)
      (name : String) (foreign : Events.External E),
      resolve env "m" = some (.pointer (some p)) →
      resolve env "fmi3Discard" = some (.integer 2) →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      program.addresses logger = some name → literals "logStatus" = some category →
      literals message = some text → program.externals name = some foreign →
      foreign.signature = Logging.signature name → ∀ behavior,
      (Events.machine program).Behaves
        (.body (.running (Runtime.stepDiscard ++ rest) env types heap) "fmi3Status" .done) behavior ↔
      (∃ events value after, foreign.execute (arguments environment category text) heap events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (arguments environment category text) heap events value after) ∧
        behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program env types rest heap p text category logger environment name foreign instanceValue statusValue
    loggerValue loggingValue environmentValue address categoryBound textBound external prototype behavior
  have entered := dispatch_reaches context program env types rest heap p text category logger environment name
    .done instanceValue statusValue loggerValue loggingValue environmentValue address categoryBound textBound
  rw [Events.internal_prefix_behaviors program entered behavior]
  apply Events.external_choices_behaviors program external
    (prototype ▸ arguments_converted context name environment category text) (fun _ after => ⟨.integer 2, after⟩)
  intro events value after executed
  exact Events.internal_prefix program (resume_reaches context program env types rest .done value after statusValue)
    (Events.return_forced program (.integer 2) after)

/-- Failure of clock progress or of the existing unit-grid duration policy.
The stop bound is checked first and remains a separate Error condition. -/
def Rejected (time step : Binary64.Value) : Prop :=
  ¬ StepGuards.Progress time (Binary64.addResult time step) ∨ ¬ StepAdmission.AdmittedDuration step

def Path [CInterface] (program : Events.Program E) (start : Typed.State)
    (heap : Heap) (p : Address) : Prop :=
  ∃ env types rest, Transition.Events.Prefix (Events.machine program) start []
      (.body (.running (Runtime.stepDiscard ++ rest) env types heap) "fmi3Status" .done) ∧
    resolve env "m" = some (.pointer (some p)) ∧ resolve env "fmi3Discard" = some (.integer 2)

/-- Both public discard causes reach the same checked block. Floor is required
only when the rounded clock advances; no solver call is needed on either path. -/
theorem public_prefix (context : ErrorContext literals) (model : Solve.FMI3Model source) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point : BitVec 64) (step time : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64),
      context.target.constants "fegetround" = none → context.target.constants "floor" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      context.target.constants "fmi3Discard" = some (.integer 2) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      (StepGuards.Progress time (Binary64.addResult time step) →
        program.externals "floor" = some (CMathCalls.floorExternal double)) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop → Rejected time step →
      Path program (.calling StepEntry.signature.name
        (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) p := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag stop integer double ordinaryRounding ordinaryFloor
    macroBound discardBound rounding floorBound defined kindValue modeValue clock stored valid enabled limit noStop rejected
  obtain ⟨types, entered⟩ := StepFailures.rounding_entry context model header program heap p buffers point
    (Binary64.toBits step).val time flag header.nearest _ integer ordinaryRounding macroBound rounding
    defined kindValue modeValue clock stored valid
  let env := StepFailures.roundingLocals p buffers point (Binary64.toBits step).val flag header.nearest
  let nextEnv := bind env "next" (.float64 (Binary64.addResult time step).encode)
  let nextTypes := CLoops.bindType types "next" .float64
  have checked := StepGuards.clock_path program env types (StepEntry.outputHeap heap buffers time)
    p time step stop (Runtime.stepGrid ++ StepAdvance.code) "fmi3Status" .done double
    (by simp [env, StepFailures.roundingLocals, StepFailures.entryLocals,
      StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [env, StepFailures.roundingLocals, StepFailures.entryLocals, StepEntry.locals, CBody.bind])
    (by simp [env, StepFailures.roundingLocals, StepFailures.entryLocals,
      StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    ((stored.load_field time "time").trans clock) ((stored.load_field time "stopDefined").trans enabled)
    (fun value chosen => (stored.load_field time "stop").trans (limit value chosen))
  simp only [StepFailures.roundingDestination, ↓reduceIte, List.nil_append] at entered
  have throughClock := entered.trans checked
  by_cases progress : StepGuards.Progress time (Binary64.addResult time step)
  · have offGrid : ¬ StepAdmission.AdmittedDuration step := by
      rcases rejected with noProgress | offGrid
      · contradiction
      · exact offGrid
    have positive : 0 < Binary64.value step := by
      cases decoded : Float64.decode point <;>
        simp only [StepEntry.InputsValid, decoded, Float64.decode_finite] at valid
      exact valid.2
    have reached : Transition.Events.Prefix (Events.machine program)
        (.calling StepEntry.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) []
        (.body (.running (Runtime.stepGrid ++ StepAdvance.code) nextEnv nextTypes
          (StepEntry.outputHeap heap buffers time)) "fmi3Status" .done) := by
      simpa only [StepGuards.clockDestination, noStop, progress, ↓reduceIte, List.nil_append] using throughClock
    have grid := StepGuards.grid_path program nextEnv nextTypes (StepEntry.outputHeap heap buffers time)
      step StepAdvance.code "fmi3Status" .done double
      (by simp [nextEnv, env, StepFailures.roundingLocals, StepFailures.entryLocals,
        StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind])
      (by simp [nextEnv, env, StepFailures.roundingLocals, StepFailures.entryLocals,
        StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind]) ordinaryFloor
      (by simp [nextEnv, env, StepFailures.roundingLocals, StepFailures.entryLocals,
        StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
      positive (floorBound progress)
    refine ⟨bind nextEnv "floored" (.finite (Binary64.floorValue step)),
      CLoops.bindType nextTypes "floored" .float64, StepAdvance.code, ?_, ?_, ?_⟩
    · simpa only [offGrid, ↓reduceIte, List.nil_append] using reached.trans grid
    · simp [nextEnv, env, StepFailures.roundingLocals, StepFailures.entryLocals,
        StepEntry.locals, CBody.bind, resolve]
    · simp [nextEnv, env, StepFailures.roundingLocals, StepFailures.entryLocals,
        StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind, resolve, constants, discardBound]
  · refine ⟨nextEnv, nextTypes, Runtime.stepGrid ++ StepAdvance.code, ?_, ?_, ?_⟩
    · simpa only [StepGuards.clockDestination, noStop, progress, ↓reduceIte, List.nil_append] using throughClock
    · simp [nextEnv, env, StepFailures.roundingLocals, StepFailures.entryLocals, StepEntry.locals, CBody.bind, resolve]
    · simp [nextEnv, env, StepFailures.roundingLocals, StepFailures.entryLocals,
        StepEntry.locals, StepEntry.parameters, StepEntry.bindings, CBody.bind, resolve, constants, discardBound]

theorem call_suppressed {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point : BitVec 64) (step time : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64) (logger : Option Address) (logging : Bool),
      context.target.constants "fegetround" = none → context.target.constants "floor" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      context.target.constants "fmi3Discard" = some (.integer 2) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      (StepGuards.Progress time (Binary64.addResult time step) →
        program.externals "floor" = some (CMathCalls.floorExternal double)) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop → Rejected time step →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves (.calling StepEntry.signature.name
        (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 2, StepEntry.outputHeap heap buffers time⟩ := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag stop integer double logger logging ordinaryRounding ordinaryFloor
    macroBound discardBound rounding floorBound defined kindValue modeValue clock stored valid enabled limit noStop rejected
    loggerValue loggingValue suppressed behavior
  obtain ⟨env, types, rest, reached, instanceValue, statusValue⟩ := public_prefix context model header
    program heap p buffers point step time flag stop integer double ordinaryRounding ordinaryFloor
    macroBound discardBound rounding floorBound defined kindValue modeValue clock stored valid enabled limit noStop rejected
  have result := suppressed_behaviors context program env types rest (StepEntry.outputHeap heap buffers time) p
    logger logging instanceValue statusValue ((stored.load_field time "logger").trans loggerValue)
    ((stored.load_field time "logging").trans loggingValue) suppressed
  exact (reached.silent_finite_behaviors (by intro history; simp [result]) behavior).trans (result behavior)

theorem call_logged {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p text category logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64)
      (environment : Option Address) (name : String) (foreign : Events.External E),
      context.target.constants "fegetround" = none → context.target.constants "floor" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      context.target.constants "fmi3Discard" = some (.integer 2) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      (StepGuards.Progress time (Binary64.addResult time step) →
        program.externals "floor" = some (CMathCalls.floorExternal double)) →
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      literals "logStatus" = some category → literals message = some text →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop → Rejected time step →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (Events.machine program).Behaves (.calling StepEntry.signature.name
        (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
      (∃ events value after, foreign.execute (arguments environment category text)
        (StepEntry.outputHeap heap buffers time) events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (arguments environment category text)
        (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program heap p text category logger buffers point step time flag stop integer double environment name foreign
    ordinaryRounding ordinaryFloor macroBound discardBound rounding floorBound defined categoryBound textBound address external
    prototype kindValue modeValue clock stored valid enabled limit noStop rejected loggerValue loggingValue environmentValue behavior
  obtain ⟨env, types, rest, reached, instanceValue, statusValue⟩ := public_prefix context model header
    program heap p buffers point step time flag stop integer double ordinaryRounding ordinaryFloor
    macroBound discardBound rounding floorBound defined kindValue modeValue clock stored valid enabled limit noStop rejected
  have result := all_behaviors context program env types rest (StepEntry.outputHeap heap buffers time) p text category logger
    environment name foreign instanceValue statusValue ((stored.load_field time "logger").trans loggerValue)
    ((stored.load_field time "logging").trans loggingValue) ((stored.load_field time "environment").trans environmentValue)
    address categoryBound textBound external prototype
  exact (reached.silent_finite_behaviors (by intro history; simp [result]) behavior).trans (result behavior)

/-- A missing callback skips the logging flag and all callback arguments. The
discard block neither terminates the instance nor changes its supplied heap. -/
theorem missing_reaches (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (heap : Heap) (p : Address) (stack : Typed.Continuation),
      resolve env "m" = some (.pointer (some p)) →
      resolve env "fmi3Discard" = some (.integer 2) →
      load heap (p.member "logger") = some (.pointer none) →
      Transition.Reaches (fun s t => Events.internalNext program s = some t)
        (.body (.running (Runtime.stepDiscard ++ rest) env types heap) "fmi3Status" stack)
        (.returning (.integer 2) heap stack) := by
  letI : CInterface := context.target
  intro program env types rest heap p stack instanceValue statusValue loggerValue
  have disabled := CNull.and_unequal_null_short_circuit
    (Runtime.field "logger") (Runtime.field "logging") env heap
    (by simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address, loggerValue])
    (by change context.target.types "void *" = some .pointer; rw [← context.types]; rfl)
  have cast : CCalls.returnCast "fmi3Status" (.integer 2) = some (.integer 2) := by
    simp [CCalls.returnCast, CBody.cast, ← context.types, convert]
  refine .next (t := .body (.running (Runtime.ret (Runtime.v "fmi3Discard") :: rest) env types heap)
    "fmi3Status" stack) ?_ ?_
  · apply Events.body_step
    simp [Runtime.stepDiscard, Runtime.log, Runtime.branch, Runtime.both, Runtime.nev,
      CLoops.next, CLoops.nextWith, CLoops.noDeclarations, CLoops.evalWith, CBody.legacyExpressions, disabled, Value.truth, boolean]
  · refine .next (t := .body (.returned ⟨.integer 2, heap⟩) "fmi3Status" stack) ?_ ?_
    · apply Events.body_step
      simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, Runtime.ret, Runtime.v, CBody.eval, CBody.evalWith, statusValue]
    · exact .next (by simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, cast]) (.refl _)

theorem missing_behaviors (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (heap : Heap) (p : Address),
      resolve env "m" = some (.pointer (some p)) →
      resolve env "fmi3Discard" = some (.integer 2) →
      load heap (p.member "logger") = some (.pointer none) → ∀ behavior,
      (Events.machine program).Behaves
        (.body (.running (Runtime.stepDiscard ++ rest) env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates [] ⟨.integer 2, heap⟩ := by
  letI : CInterface := context.target
  intro program env types rest heap p instanceValue statusValue loggerValue behavior
  exact (Events.internal_prefix program
    (missing_reaches context program env types rest heap p .done instanceValue statusValue loggerValue)
    (Events.return_forced program (.integer 2) heap)).behaviors behavior

theorem path_missing_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (start : Typed.State) (heap : Heap) (p : Address),
      Path program start heap p →
      load heap (p.member "logger") = some (.pointer none) → ∀ behavior,
      (Events.machine program).Behaves start behavior ↔
      behavior = .terminates [] ⟨.integer 2, heap⟩ := by
  letI : CInterface := context.target
  intro program start heap p certified loggerValue behavior
  obtain ⟨env, types, rest, path, instanceValue, statusValue⟩ := certified
  have result := missing_behaviors context program env types rest heap p
    instanceValue statusValue loggerValue
  exact (path.silent_finite_behaviors (by intro history; simp [result]) behavior).trans (result behavior)

open StepFailures in
/-- A nonprogressing or overflowing clock reaches the emitted discard block
without executing floor or requiring a floor binding. -/
theorem nonprogress_prefix_for_tail {E : Type} (context : ErrorContext literals)
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
      context.target.constants "fmi3Discard" = some (.integer 2) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      ¬ StepGuards.Progress time (Binary64.addResult time step) →
      StepDiscard.Path program
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) p := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag stop integer ordinary macroBound discardBound rounding
    defined kindValue modeValue clock stored valid enabled limit noStop noProgress
  obtain ⟨types, path⟩ := clock_entry_for_tail context fn tail signature body closed header
    program heap p buffers point step time flag stop integer ordinary macroBound rounding defined
    kindValue modeValue clock stored valid enabled limit
  refine ⟨CBody.bind (roundingLocals p buffers point (Binary64.toBits step).val flag header.nearest)
    "next" (.float64 (Binary64.addResult time step).encode), CLoops.bindType types "next" .float64,
    tail, ?_, ?_, ?_⟩
  · simpa only [StepGuards.clockDestination, noStop, noProgress, ↓reduceIte] using path
  · simp [roundingLocals, entryLocals, StepEntry.locals, CBody.bind, resolve]
  · simp [roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters,
      StepEntry.bindings, CBody.bind, resolve, constants, discardBound]

theorem path_suppressed_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (start : Typed.State) (heap : Heap) (p : Address)
      (logger : Option Address) (logging : Bool),
      Path program start heap p →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves start behavior ↔
      behavior = .terminates [] ⟨.integer 2, heap⟩ := by
  letI : CInterface := context.target
  intro program start heap p logger logging certified loggerValue loggingValue suppressed behavior
  obtain ⟨env, types, rest, path, instanceValue, statusValue⟩ := certified
  have result := suppressed_behaviors context program env types rest heap p logger logging
    instanceValue statusValue loggerValue loggingValue suppressed
  exact (path.silent_finite_behaviors (by intro history; simp [result]) behavior).trans (result behavior)

theorem path_all_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (start : Typed.State) (heap : Heap) (p text category logger : Address)
      (environment : Option Address) (name : String) (foreign : Events.External E),
      Path program start heap p →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      program.addresses logger = some name → literals "logStatus" = some category →
      literals message = some text → program.externals name = some foreign →
      foreign.signature = Logging.signature name → ∀ behavior,
      (Events.machine program).Behaves start behavior ↔
      (∃ events value after, foreign.execute (arguments environment category text) heap events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (arguments environment category text) heap events value after) ∧
        behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program start heap p text category logger environment name foreign certified
    loggerValue loggingValue environmentValue address categoryBound textBound external prototype behavior
  obtain ⟨env, types, rest, path, instanceValue, statusValue⟩ := certified
  have result := all_behaviors context program env types rest heap p text category logger environment
    name foreign instanceValue statusValue loggerValue loggingValue environmentValue address
    categoryBound textBound external prototype
  exact (path.silent_finite_behaviors (by intro history; simp [result]) behavior).trans (result behavior)

open StepFailures in
/-- Both discard causes for any actual step body. Floor bindings are required
only if the rounded clock advances; stop rejection remains earlier. -/
theorem public_prefix_for_tail {E : Type} (context : ErrorContext literals)
    (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tail))
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) (header : CFenv.Header) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
      (point : BitVec 64) (step time : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      context.target.constants "fmi3Discard" = some (.integer 2) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      (StepGuards.Progress time (Binary64.addResult time step) →
        context.target.constants "floor" = none ∧
        program.externals "floor" = some (CMathCalls.floorExternal double)) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop → Rejected time step →
      Path program (.calling fn.signature.name
        (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) p := by
  letI : CInterface := context.target
  intro program heap p buffers point step time flag stop integer double ordinary macroBound discardBound
    rounding floorBound defined kindValue modeValue clock stored valid enabled limit noStop rejected
  by_cases progress : StepGuards.Progress time (Binary64.addResult time step)
  · obtain ⟨types, path⟩ := clock_entry_for_tail context fn (Runtime.stepGrid ++ tail)
      signature (by simpa only [List.append_assoc] using body) closed header program heap p buffers
      point step time flag stop integer ordinary macroBound rounding defined kindValue modeValue
      clock stored valid enabled limit
    let env := CBody.bind (roundingLocals p buffers point (Binary64.toBits step).val flag header.nearest)
      "next" (.float64 (Binary64.addResult time step).encode)
    let nextTypes := CLoops.bindType types "next" .float64
    have offGrid : ¬ StepAdmission.AdmittedDuration step := by
      rcases rejected with noProgress | offGrid
      · contradiction
      · exact offGrid
    have positive : 0 < Binary64.value step := by
      cases decoded : Float64.decode point <;>
        simp only [StepEntry.InputsValid, decoded, Float64.decode_finite] at valid
      exact valid.2
    have reached : Transition.Events.Prefix (Events.machine program)
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs) heap .done) []
        (.body (.running (Runtime.stepGrid ++ tail) env nextTypes
          (StepEntry.outputHeap heap buffers time)) "fmi3Status" .done) := by
      simpa only [StepGuards.clockDestination, noStop, progress, ↓reduceIte] using path
    have grid := StepGuards.grid_path program env nextTypes (StepEntry.outputHeap heap buffers time)
      step tail "fmi3Status" .done double
      (by simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters,
        StepEntry.bindings, CBody.bind])
      (by simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) (floorBound progress).1
      (by simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters,
        StepEntry.bindings, CBody.bind, Value.finite]) positive (floorBound progress).2
    refine ⟨CBody.bind env "floored" (.finite (Binary64.floorValue step)),
      CLoops.bindType nextTypes "floored" .float64, tail, ?_, ?_, ?_⟩
    · simpa only [offGrid, ↓reduceIte, List.nil_append] using reached.trans grid
    · simp [env, roundingLocals, entryLocals, StepEntry.locals, CBody.bind, resolve]
    · simp [env, roundingLocals, entryLocals, StepEntry.locals, StepEntry.parameters,
        StepEntry.bindings, CBody.bind, resolve, constants, discardBound]
  · exact nonprogress_prefix_for_tail context fn (Runtime.stepGrid ++ tail)
      signature (by simpa only [List.append_assoc] using body) closed header program heap p buffers
      point step time flag stop integer ordinary macroBound discardBound rounding defined kindValue modeValue
      clock stored valid enabled limit noStop progress

structure DiscardRejectionContract (fn : Function) : Prop where
  silent : ∀ (literals : CLiteralAddresses) {E : Type}
      (context : ErrorContext literals) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64) (logger : Option Address) (logging : Bool),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      context.target.constants "fmi3Discard" = some (.integer 2) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      (StepGuards.Progress time (Binary64.addResult time step) →
        context.target.constants "floor" = none ∧
        program.externals "floor" = some (CMathCalls.floorExternal double)) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      Rejected time step →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs)
          heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 2, StepEntry.outputHeap heap buffers time⟩
  logged : ∀ (literals : CLiteralAddresses) {E : Type}
      (context : ErrorContext literals) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p text category logger : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64)
      (environment : Option Address) (name : String) (foreign : Events.External E),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      context.target.constants "fmi3Discard" = some (.integer 2) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      (StepGuards.Progress time (Binary64.addResult time step) →
        context.target.constants "floor" = none ∧
        program.externals "floor" = some (CMathCalls.floorExternal double)) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      Rejected time step →
      literals "logStatus" = some category → literals message = some text →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs)
          heap .done) behavior ↔
      (∃ events value after, foreign.execute (arguments environment category text)
        (StepEntry.outputHeap heap buffers time) events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (arguments environment category text)
        (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong [])
  missing : ∀ (literals : CLiteralAddresses) {E : Type}
      (context : ErrorContext literals) (header : CFenv.Header),
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (heap : Heap) (p : Address)
      (buffers : StepEntry.Buffers) (point : BitVec 64) (step time : Binary64.Value)
      (flag : Bool) (stop : Option Binary64.Value)
      (integer : context.target.types "int" = some .int32)
      (double : context.target.types "double" = some .float64),
      context.target.constants "fegetround" = none →
      context.target.constants "FE_TONEAREST" = some (.integer header.nearest) →
      context.target.constants "fmi3Discard" = some (.integer 2) →
      program.externals "fegetround" = some (CMathCalls.roundingExternal integer header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      (StepGuards.Progress time (Binary64.addResult time step) →
        context.target.constants "floor" = none ∧
        program.externals "floor" = some (CMathCalls.floorExternal double)) →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      load heap (p.member "kind") = some (.integer 1) →
      load heap (p.member "mode") = some (.integer 4) →
      load heap (p.member "time") = some (.finite time) → StepArguments.Storage heap p buffers →
      StepEntry.InputsValid point (Binary64.toBits step).val time →
      load heap (p.member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      Rejected time step →
      load heap (p.member "logger") = some (.pointer none) → ∀ behavior,
      (Events.machine program).Behaves
        (.calling fn.signature.name
          (StepEntry.arguments (some p) point (Binary64.toBits step).val flag buffers.outputs)
          heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 2, StepEntry.outputHeap heap buffers time⟩

theorem discard_rejection_contract (fn : Function) (tail : List Stmt)
    (signature : fn.signature = StepEntry.signature)
    (body : fn.body = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tail))
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true) :
    DiscardRejectionContract fn where
  silent := by
    intro literals E context header program heap p buffers point step time flag stop integer double logger logging
      ordinary macroBound discardBound rounding floorBound defined kindValue modeValue clock stored valid enabled
      limit noStop rejected loggerValue loggingValue suppressed behavior
    letI : CInterface := context.target
    have path := public_prefix_for_tail context fn tail signature body closed header
      program heap p buffers point step time flag stop integer double ordinary macroBound discardBound rounding
      floorBound defined kindValue modeValue clock stored valid enabled limit noStop rejected
    exact path_suppressed_behaviors context program _ (StepEntry.outputHeap heap buffers time) p
      logger logging path ((stored.load_field time "logger").trans loggerValue)
      ((stored.load_field time "logging").trans loggingValue) suppressed behavior
  logged := by
    intro literals E context header program heap p text category logger buffers point step time flag stop
      integer double environment name foreign ordinary macroBound discardBound rounding floorBound defined kindValue
      modeValue clock stored valid enabled limit noStop rejected categoryBound textBound address external
      prototype loggerValue loggingValue environmentValue behavior
    letI : CInterface := context.target
    have path := public_prefix_for_tail context fn tail signature body closed header
      program heap p buffers point step time flag stop integer double ordinary macroBound discardBound rounding
      floorBound defined kindValue modeValue clock stored valid enabled limit noStop rejected
    exact path_all_behaviors context program _ (StepEntry.outputHeap heap buffers time) p text category
      logger environment name foreign path ((stored.load_field time "logger").trans loggerValue)
      ((stored.load_field time "logging").trans loggingValue)
      ((stored.load_field time "environment").trans environmentValue)
      address categoryBound textBound external prototype behavior
  missing := by
    intro literals E context header program heap p buffers point step time flag stop integer double
      ordinary macroBound discardBound rounding floorBound defined kindValue modeValue clock stored valid enabled
      limit noStop rejected loggerValue behavior
    letI : CInterface := context.target
    have path := public_prefix_for_tail context fn tail signature body closed header
      program heap p buffers point step time flag stop integer double ordinary macroBound discardBound rounding
      floorBound defined kindValue modeValue clock stored valid enabled limit noStop rejected
    exact path_missing_behaviors context program _ (StepEntry.outputHeap heap buffers time) p
      path ((stored.load_field time "logger").trans loggerValue) behavior

end Rumoca.FMI3.StepDiscard
end
