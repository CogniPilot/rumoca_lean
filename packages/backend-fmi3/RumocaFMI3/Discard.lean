import RumocaFMI3.DiscardCode
import RumocaFMI3.ErrorContext

/-! Scheduler-level execution facts for the reusable FMI discard diagnostic.
The callback request is the boundary: before it, the body leaves the supplied
heap unchanged; no callback result or callback frame is assumed here. -/
noncomputable section
namespace Rumoca.FMI3.Discard
open CTree CMemory CBody CCalls
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def arguments (environment : Option Address) (category text : Address) : List Value :=
  [.pointer environment, .integer 2, .pointer (some category), .pointer (some text)]

def continuation (env : Locals) (types : CLoops.Types) (rest : List Stmt)
    (stack : Typed.Continuation) :=
  Typed.Continuation.caller .discard (Runtime.ret (Runtime.v "fmi3Discard") :: rest)
    env types "fmi3Status" stack

def logCall (message : String) : Stmt := Stmt.eval (.call (Runtime.field "logger")
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
  · simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, CLoops.nextWith,
      CLoops.evalWith, CBody.legacyExpressions, Runtime.ret, Runtime.v, CBody.eval, CBody.evalWith,
      statusValue]
  · exact .next (by simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, cast])
      (.refl _)

theorem suppressed_reaches (context : ErrorContext literals) (message : String) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (heap : Heap) (p : Address) (logger : Option Address) (logging : Bool)
      (stack : Typed.Continuation),
      resolve env "m" = some (.pointer (some p)) →
      resolve env "fmi3Discard" = some (.integer 2) →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) →
      Transition.Reaches (fun s t => Events.internalNext program s = some t)
        (.body (.running (body message ++ rest) env types heap) "fmi3Status" stack)
        (.returning (.integer 2) heap stack) := by
  letI : CInterface := context.target
  intro program env types rest heap p logger logging stack instanceValue statusValue loggerValue
    loggingValue suppressed
  have disabled : eval env heap (Runtime.both
      (Runtime.nev (Runtime.field "logger") Expr.nullPointer) (Runtime.field "logging")) =
      some (.integer 0) := by
    change eval env heap (.bin .and (.bin .ne (Runtime.field "logger") Expr.nullPointer)
      (Runtime.field "logging")) = _
    rw [CNull.and_unequal_null_eval _ _ env heap logger
      (by simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue,
        CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address, loggerValue])
      (by change context.target.types "void *" = some .pointer; rw [← context.types]; rfl)]
    rcases suppressed with rfl | rfl
    · simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue,
        CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address,
        loggerValue, Value.truth, boolean]
    · cases logger <;>
        simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue,
          CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address,
          loggerValue, loggingValue, Value.truth, boolean]
  simp only [Runtime.both, Runtime.nev] at disabled
  have cast : CCalls.returnCast "fmi3Status" (.integer 2) = some (.integer 2) := by
    simp [CCalls.returnCast, CBody.cast, ← context.types, convert]
  refine .next (t := .body (.running (Runtime.ret (Runtime.v "fmi3Discard") :: rest) env types heap)
    "fmi3Status" stack) ?_ ?_
  · apply Events.body_step
    simp [body, Runtime.log, Runtime.branch, Runtime.both, Runtime.nev, CLoops.next,
      CLoops.nextWith, CLoops.noDeclarations, CLoops.evalWith, CBody.legacyExpressions, disabled,
      Value.truth]
  · refine .next (t := .body (.returned ⟨.integer 2, heap⟩) "fmi3Status" stack) ?_ ?_
    · apply Events.body_step
      simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, Runtime.ret,
        Runtime.v, CBody.eval, CBody.evalWith, statusValue]
    · exact .next (by simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, cast])
        (.refl _)

theorem dispatch_reaches (context : ErrorContext literals) (message : String) :
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
        (.body (.running (body message ++ rest) env types heap) "fmi3Status" stack)
        (.calling name (arguments environment category text) heap
          (continuation env types rest stack)) := by
  letI : CInterface := context.target
  intro program env types rest heap p text category logger environment name stack instanceValue
    statusValue loggerValue loggingValue environmentValue address categoryLiteral textLiteral
  have categoryBound : CInterface.literals "logStatus" = some category :=
    context.bytes ▸ categoryLiteral
  have textBound : CInterface.literals message = some text := context.bytes ▸ textLiteral
  have enabled : eval env heap (Runtime.both
      (Runtime.nev (Runtime.field "logger") Expr.nullPointer) (Runtime.field "logging")) =
      some (.integer 1) := by
    change eval env heap (.bin .and (.bin .ne (Runtime.field "logger") Expr.nullPointer)
      (Runtime.field "logging")) = _
    rw [CNull.and_unequal_null_eval _ _ env heap (some logger)
      (by simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue,
        CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address, loggerValue])
      (by change context.target.types "void *" = some .pointer; rw [← context.types]; rfl)]
    simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue,
      CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address,
      loggerValue, loggingValue, Value.truth, boolean]
  simp only [Runtime.both, Runtime.nev] at enabled
  have resolved : Events.resolve program env heap (Runtime.field "logger") = some name := by
    simp [Events.resolve, Events.resolveWith, CCalls.Indirect.resolveWith, CBody.legacyExpressions,
      Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue,
      CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceValue, Value.address,
      loggerValue, CCalls.Indirect.valueTarget, address]
  have values : CCalls.arguments env heap
      [Runtime.field "environment", Runtime.v "fmi3Discard", .str "logStatus", .str message] =
      some (arguments environment category text) := by
    simp [CCalls.arguments, CCalls.argumentsWith, CBody.legacyExpressions, Runtime.field, Runtime.v,
      CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt,
      CDeclaredMembers.fieldAt, instanceValue, statusValue, Value.address, environmentValue,
      categoryBound, textBound, arguments, argumentsWith, CBody.legacyExpressions]
  let tail := Runtime.ret (Runtime.v "fmi3Discard") :: rest
  have blocked : CLoops.next (.running (logCall message :: tail) env types heap) = none := by
    simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, logCall,
      Runtime.field, Runtime.v, CBody.eval, CBody.evalWith]
  refine .next (t := .body (.running (logCall message :: tail) env types heap)
    "fmi3Status" stack) ?_ ?_
  · apply Events.body_step
    simp [body, Runtime.log, Runtime.branch, Runtime.both, Runtime.nev, CLoops.noDeclarations,
      CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, enabled,
      Value.truth, logCall, tail]
  · refine .next ?_ (.refl _)
    simp only [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, blocked]
    simp [Events.enterCallWith, logCall, CCalls.Indirect.operand, resolved, values, continuation, tail]

theorem suppressed_behaviors (context : ErrorContext literals) (message : String) :
    letI : CInterface := context.target
    ∀ (program : Events.Program E) (env : Locals) (types : CLoops.Types) (rest : List Stmt)
      (heap : Heap) (p : Address) (logger : Option Address) (logging : Bool),
      resolve env "m" = some (.pointer (some p)) →
      resolve env "fmi3Discard" = some (.integer 2) →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves
        (.body (.running (body message ++ rest) env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates [] ⟨.integer 2, heap⟩ := by
  letI : CInterface := context.target
  intro program env types rest heap p logger logging instanceValue statusValue loggerValue loggingValue suppressed behavior
  exact (Events.internal_prefix program
    (suppressed_reaches context message program env types rest heap p logger logging .done
      instanceValue statusValue loggerValue loggingValue suppressed)
    (Events.return_forced program (.integer 2) heap)).behaviors behavior

theorem logged_behaviors (context : ErrorContext literals) (message : String) :
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
        (.body (.running (body message ++ rest) env types heap) "fmi3Status" .done) behavior ↔
      (∃ events value after, foreign.execute (arguments environment category text) heap events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (arguments environment category text) heap events value after) ∧
        behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program env types rest heap p text category logger environment name foreign instanceValue statusValue
    loggerValue loggingValue environmentValue address categoryBound textBound external prototype behavior
  have entered := dispatch_reaches context message program env types rest heap p text category logger environment
    name .done instanceValue statusValue loggerValue loggingValue environmentValue address categoryBound textBound
  rw [Events.internal_prefix_behaviors program entered behavior]
  apply Events.external_choices_behaviors program external
    (prototype ▸ arguments_converted context name environment category text) (fun _ after => ⟨.integer 2, after⟩)
  intro events value after executed
  exact Events.internal_prefix program (resume_reaches context program env types rest .done value after statusValue)
    (Events.return_forced program (.integer 2) after)

end Rumoca.FMI3.Discard
