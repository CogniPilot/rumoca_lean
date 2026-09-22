import RumocaFMI3.ErrorContext

/-! Complete failure-helper calls under explicit local interface agreement.
Static objects and rounding headers reuse the same proofs; callbacks retain
every represented outcome and memory effect. -/
noncomputable section
namespace Rumoca.FMI3.StaticErrors
open CTree CMemory CBody StaticFactory CLiteral.Interface

/-- The nullable callback and Boolean flag exhaust the represented logging
domain. Missing callback support is handled defensively by the emitted guard. -/
theorem logging_cases (logger : Option Address) (logging : Bool) :
    (logger = none ∨ logging = false) ∨ ∃ address, logger = some address ∧ logging = true := by
  cases logger <;> cases logging <;> simp

theorem helper_agrees (context : ErrorContext literals) :
    CodeAgrees (cInterface literals) context.target Runtime.helpers[0].body := context.helper

theorem helper_parameters (context : ErrorContext literals)
    (p message : Address) :
    @CCalls.parameters context.target Runtime.helpers[0].signature.parameters
      [.pointer (some p), .pointer (some message)] = some (ErrorCalls.failureEnv p message) :=
  (parameters_agreement (cInterface literals) context.target
    context.types _ _).symm.trans
    (ErrorCalls.failure_parameters (static := ⟨literals⟩) p message)

/-- Entry and the mode/logging guard reach the actual indirect callback site.
The callback itself has not been executed by this finite internal prefix. -/
theorem dispatch_reaches {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap)
      (p message category logger : Address) (environment : Option Address)
      (old : Option Value) (name : String) (stack : CCalls.Typed.Continuation),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      program.addresses logger = some name → literals "logStatus" = some category →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      ∃ types, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fail" [.pointer (some p), .pointer (some message)] heap stack)
        (.calling name (Logging.arguments environment category message)
          (LifecycleBodies.writeMode heap p .terminated)
          (Logging.failureContinuation p message types stack)) := by
  letI : CInterface := context.target
  intro program heap p message category logger environment old name stack defined address literal hm hl hg he
  let env := ErrorCalls.failureEnv p message
  have pure := ErrorBodies.failure_dispatch_run (static := ⟨literals⟩) env heap p old (some logger) true
    (by simp [env, ErrorCalls.failureEnv, CBody.bind, resolve]) hm hl hg
  simp only [Option.isSome_some, Bool.and_self, ↓reduceIte] at pure
  have transferred := (body_run_agreement (cInterface literals) context.target
    context.types context.bytes 2
    (.running Runtime.helpers[0].body env heap) (helper_agrees context)).symm.trans pure
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] env env heap
    (LifecycleBodies.writeMode heap p .terminated)
    [ErrorBodies.logCall, Runtime.ret (Runtime.v "fmi3Error")] stack 2 defined
    (helper_parameters context p message)
    (BodyEmbedding.helpers_closed _ (by simp [Runtime.helpers])) transferred
  have hp : resolve env "m" = some (.pointer (some p)) := by
    simp [env, ErrorCalls.failureEnv, CBody.bind, resolve]
  have loggerAfter : load (LifecycleBodies.writeMode heap p .terminated) (p.member "logger") =
      some (.pointer (some logger)) := by
    simpa only [load, LifecycleBodies.write_frame heap p (p.member "logger") .terminated (by simp)] using hl
  have environmentAfter : load (LifecycleBodies.writeMode heap p .terminated) (p.member "environment") =
      some (.pointer environment) := by
    simpa only [load, LifecycleBodies.write_frame heap p (p.member "environment") .terminated (by simp)] using he
  have resolved : CCalls.Events.resolve program env (LifecycleBodies.writeMode heap p .terminated)
      (Runtime.field "logger") = some name := by
    simp [CCalls.Events.resolve, CCalls.Indirect.resolve, Runtime.field, Runtime.v,
      CBody.eval, hp, Value.address, loggerAfter, CCalls.Indirect.valueTarget, address]
  have errorBound : CInterface.constants "fmi3Error" = some (.integer 3) := context.error
  have categoryBound : CInterface.literals "logStatus" = some category := context.bytes ▸ literal
  have values : CCalls.arguments env (LifecycleBodies.writeMode heap p .terminated)
      [Runtime.field "environment", Runtime.v "fmi3Error", .str "logStatus", Runtime.v "message"] =
      some (Logging.arguments environment category message) := by
    simp [CCalls.arguments, Runtime.field, Runtime.v, CBody.eval, Value.address,
      environmentAfter, categoryBound, errorBound, Logging.arguments, env, ErrorCalls.failureEnv,
      CBody.bind, resolve, constants]
  have blocked : CLoops.next (.running [ErrorBodies.logCall, Runtime.ret (Runtime.v "fmi3Error")]
      env types (LifecycleBodies.writeMode heap p .terminated)) = none := by
    simp [CLoops.next, CLoops.eval, ErrorBodies.logCall, Runtime.field, Runtime.v, CBody.eval]
  have entered : CCalls.Events.internalNext program
      (.body (.running [ErrorBodies.logCall, Runtime.ret (Runtime.v "fmi3Error")]
        env types (LifecycleBodies.writeMode heap p .terminated)) "fmi3Status" stack) =
      some (.calling name (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) (Logging.failureContinuation p message types stack)) := by
    simp only [CCalls.Events.internalNext, CCalls.Typed.nextWith, blocked]
    simp [CCalls.Events.enterCall, ErrorBodies.logCall, CCalls.Indirect.operand,
      resolved, values, Logging.failureContinuation, env]
  exact ⟨types, reached.trans (.next entered (.refl _))⟩

theorem resume_reaches {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (p message : Address) (types : CLoops.Types)
      (stack : CCalls.Typed.Continuation) (value : Value) (heap : Heap),
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.returning value heap (Logging.failureContinuation p message types stack))
        (.returning (.integer 3) heap stack) := by
  letI : CInterface := context.target
  intro program p message types stack value heap
  let env := ErrorCalls.failureEnv p message
  have errorValue : resolve env "fmi3Error" = some (.integer 3) := by
    simp [env, ErrorCalls.failureEnv, CBody.bind, resolve, constants, context.error]
  refine .next (t := .body (.running [Runtime.ret (Runtime.v "fmi3Error")] env types heap)
    "fmi3Status" stack) (by rfl) ?_
  refine .next (t := .body (.returned ⟨.integer 3, heap⟩) "fmi3Status" stack) ?_ ?_
  · simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
      Runtime.ret, Runtime.v, CBody.eval, errorValue]
  · exact .next (by simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, context.error_cast]) (.refl _)

/-- All enabled callback outcomes, including an absent outcome, are retained.
This does not model the native callback's internal execution or reentry. -/
theorem helper_all_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap)
      (p message category logger : Address) (environment : Option Address)
      (old : Option Value) (name : String) (foreign : CCalls.Events.External E),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name → literals "logStatus" = some category →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling "fail" [.pointer (some p), .pointer (some message)] heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program heap p message category logger environment old name foreign
    defined address external prototype literal hm hl hg he behavior
  obtain ⟨types, dispatched⟩ := dispatch_reaches context program heap p message category logger
    environment old name .done defined address literal hm hl hg he
  rw [CCalls.Events.internal_prefix_behaviors program dispatched behavior]
  apply CCalls.Events.external_choices_behaviors program external
    (prototype ▸ context.logging_arguments name environment category message)
    (fun _ after => ⟨.integer 3, after⟩)
  intro events value after executed
  exact CCalls.Events.internal_prefix program
    (resume_reaches context program p message types .done value after)
    (CCalls.Events.return_forced program (.integer 3) after)

theorem helper_suppressed_reaches {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (old : Option Value) (logger : Option Address) (logging : Bool) (stack : CCalls.Typed.Continuation),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) →
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fail" [.pointer (some p), .pointer (some message)] heap stack)
        (.returning (.integer 3) (LifecycleBodies.writeMode heap p .terminated) stack) := by
  letI : CInterface := context.target
  intro program heap p message old logger logging stack defined hm hl hg suppressed
  have off : (logger.isSome && logging) = false := by
    rcases suppressed with rfl | rfl <;> simp
  have pure : @CBody.run (cInterface literals) 3
      (.running Runtime.helpers[0].body (ErrorCalls.failureEnv p message) heap) =
      some (.returned ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩) := by
    rw [show 3 = 2 + 1 from rfl, @CBody.run_add (cInterface literals),
      ErrorBodies.failure_dispatch_run (static := ⟨literals⟩) (ErrorCalls.failureEnv p message)
        heap p old logger logging (by simp [ErrorCalls.failureEnv, CBody.bind, resolve]) hm hl hg,
      off]
    simp [run, next, Runtime.ret, Runtime.v, eval, ErrorCalls.failureEnv, CBody.bind, resolve, constants]
  have transferred := (body_run_agreement (cInterface literals) context.target
    context.types context.bytes 3
    (.running Runtime.helpers[0].body (ErrorCalls.failureEnv p message) heap)
    (helper_agrees context)).symm.trans pure
  exact CCalls.Events.body_call_reaches program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] (ErrorCalls.failureEnv p message) heap
    ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ (.integer 3) stack 3 defined
    (helper_parameters context p message)
    (BodyEmbedding.helpers_closed _ (by simp [Runtime.helpers])) transferred context.error_cast

theorem helper_silent_reaches {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (old : Option Value) (logger : Option Address) (stack : CCalls.Typed.Continuation),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (.integer 0) →
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fail" [.pointer (some p), .pointer (some message)] heap stack)
        (.returning (.integer 3) (LifecycleBodies.writeMode heap p .terminated) stack) := by
  letI : CInterface := context.target
  intro program heap p message old logger stack defined hm hl hg
  exact helper_suppressed_reaches context program heap p message old logger false stack
    defined hm hl hg (Or.inr rfl)

theorem helper_silent_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (old : Option Value) (logger : Option Address),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (.integer 0) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling "fail" [.pointer (some p), .pointer (some message)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := context.target
  intro program heap p message old logger defined hm hl hg behavior
  exact (CCalls.Events.internal_prefix program
    (helper_silent_reaches context program heap p message old logger .done defined hm hl hg)
    (CCalls.Events.return_forced program (.integer 3) (LifecycleBodies.writeMode heap p .terminated))).behaviors behavior

/-- Prefix transport needs agreement only for the current function, including
its failure statement. It imposes no condition on unrelated factory bodies. -/
theorem failure_prefix (context : ErrorContext literals)
    (fn : Function) (args : List Value) (before after : Heap) (p : Address) (text : String)
    (agrees : CodeAgrees (cInterface literals) context.target fn.body)
    (certified : @GuardedCalls.FailurePrefix (cInterface literals) fn args before p text after) :
    @GuardedCalls.FailurePrefix context.target fn args before p text after := by
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ := certified
  refine ⟨status, closed, env, later, tail, steps, ?_, ?_, unshadowed, ?_⟩
  · exact (parameters_agreement (cInterface literals) context.target
      context.types _ _).symm.trans bound
  · exact (body_run_agreement (cInterface literals) context.target
      context.types context.bytes steps (.running fn.body env before) agrees).symm.trans executed
  · simpa [resolve, constants, context.instance_binding] using instanceBound

theorem statement_entry {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (env : Locals) (types : CLoops.Types)
      (code : List Stmt) (text : String) (heap : Heap) (p message : Address)
      (stack : CCalls.Typed.Continuation),
      env "fail" = none → resolve env "m" = some (.pointer (some p)) →
      literals text = some message →
      CCalls.Events.internalNext program
        (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" stack) =
      some (.calling "fail" [.pointer (some p), .pointer (some message)] heap
        (.caller .ret code env types "fmi3Status" stack)) := by
  letI : CInterface := context.target
  intro program env types code text heap p message stack unshadowed instanceBound messageBound
  have named : CInterface.constants "fail" = none := context.ordinary
  have literal : CInterface.literals text = some message := context.bytes ▸ messageBound
  have resolved : CCalls.Events.resolve program env heap (Runtime.v "fail") = some "fail" := by
    simp [CCalls.Events.resolve, CCalls.Indirect.resolve, Runtime.v,
      resolve, unshadowed, constants, named]
  have values : CCalls.arguments env heap [Runtime.v "m", .str text] =
      some [.pointer (some p), .pointer (some message)] := by
    simp [CCalls.arguments, Runtime.v, CBody.eval, instanceBound, literal]
  have blocked : CLoops.next (.running (Runtime.fail text :: code) env types heap) = none := by
    simp [CLoops.next, CLoops.eval, Runtime.fail, Runtime.ret, Runtime.call, Runtime.v, CBody.eval]
  simp only [CCalls.Events.internalNext, CCalls.Typed.nextWith, blocked]
  simp [CCalls.Events.enterCall, Runtime.fail, Runtime.ret, Runtime.call,
    CCalls.Indirect.operand, resolved, values]


/-- A reached failure statement retains every represented callback outcome.
Its caller may have performed ordinary library calls before reaching it. -/
theorem statement_all_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (env : Locals) (types : CLoops.Types)
      (code : List Stmt) (text : String) (heap : Heap)
      (p message category logger : Address) (environment : Option Address)
      (old : Option Value) (name : String) (foreign : CCalls.Events.External E),
      env "fail" = none → resolve env "m" = some (.pointer (some p)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message → program.addresses logger = some name →
      program.externals name = some foreign → foreign.signature = Logging.signature name →
      literals "logStatus" = some category →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" .done) behavior ↔
      (∃ events value final, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value final ∧
        behavior = .terminates events ⟨.integer 3, final⟩) ∨
      ((∀ events value final, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value final) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program env types code text heap p message category logger environment old name foreign
    unshadowed instanceBound helper messageBound address external prototype literal hm hl hg he behavior
  let saved := CCalls.Typed.Continuation.caller .ret code env types "fmi3Status" .done
  obtain ⟨helperTypes, dispatched⟩ := dispatch_reaches context program heap p message category logger
    environment old name saved helper address literal hm hl hg he
  have path := Transition.Reaches.next (step := fun s t => CCalls.Events.internalNext program s = some t)
    (statement_entry context program env types code text heap p message .done
      unshadowed instanceBound messageBound) dispatched
  rw [CCalls.Events.internal_prefix_behaviors program path behavior]
  apply CCalls.Events.external_choices_behaviors program external
    (prototype ▸ context.logging_arguments name environment category message)
    (fun _ final => ⟨.integer 3, final⟩)
  intro events value final callback
  apply CCalls.Events.internal_prefix program
    (resume_reaches context program p message helperTypes saved value final)
  exact CCalls.Events.internal_prefix program (.next
    (by simp [CCalls.Events.internalNext, CCalls.Typed.nextWith,
      CCalls.Typed.resume, saved, context.error_cast]) (.refl _))
    (CCalls.Events.return_forced program (.integer 3) final)

/-- Disabled logging or a missing logger returns Error after the mode write,
without a callback assumption or effects on other memory cells. -/
theorem statement_suppressed_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (env : Locals) (types : CLoops.Types)
      (code : List Stmt) (text : String) (heap : Heap) (p message : Address)
      (old : Option Value) (logger : Option Address) (logging : Bool),
      env "fail" = none → resolve env "m" = some (.pointer (some p)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := context.target
  intro program env types code text heap p message old logger logging
    unshadowed instanceBound helper messageBound hm hl hg suppressed behavior
  let saved := CCalls.Typed.Continuation.caller .ret code env types "fmi3Status" .done
  have dispatched := helper_suppressed_reaches context program heap p message old logger logging
    saved helper hm hl hg suppressed
  have path := Transition.Reaches.next (step := fun s t => CCalls.Events.internalNext program s = some t)
    (statement_entry context program env types code text heap p message .done
      unshadowed instanceBound messageBound) dispatched
  exact (CCalls.Events.internal_prefix program path
    (CCalls.Events.internal_prefix program (.next
      (by simp [CCalls.Events.internalNext, CCalls.Typed.nextWith,
        CCalls.Typed.resume, saved, context.error_cast]) (.refl _))
      (CCalls.Events.return_forced program (.integer 3) (LifecycleBodies.writeMode heap p .terminated)))).behaviors behavior

/-- A derived silent execution prefix ending at the actual error-helper call.
Unlike a pure body run, this relation also composes ordinary library calls. -/
def FailurePath [CInterface] (program : CCalls.Events.Program E) (start : CCalls.Typed.State)
    (heap : Heap) (p : Address) (message : String) : Prop :=
  ∃ env types code, Transition.Events.Prefix (CCalls.Events.machine program) start []
      (.body (.running (Runtime.fail message :: code) env types heap) "fmi3Status" .done) ∧
    env "fail" = none ∧ resolve env "m" = some (.pointer (some p))

theorem path_suppressed_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (start : CCalls.Typed.State) (heap : Heap)
      (p message : Address) (text : String) (old : Option Value) (logger : Option Address) (logging : Bool),
      FailurePath program start heap p text →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message → heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves start behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := context.target
  intro program start heap p message text old logger logging path helper literal mode loggerValue loggingValue suppressed
  obtain ⟨env, types, code, reached, unshadowed, instanceBound⟩ := path
  have result := statement_suppressed_behaviors context program env types code text heap p message old
    logger logging unshadowed instanceBound helper literal mode loggerValue loggingValue suppressed
  intro behavior
  exact (reached.silent_finite_behaviors (by intro history; simp [result]) behavior).trans (result behavior)

theorem path_all_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (start : CCalls.Typed.State) (heap : Heap)
      (p message category logger : Address) (text name : String) (environment : Option Address)
      (old : Option Value) (foreign : CCalls.Events.External E),
      FailurePath program start heap p text →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message → program.addresses logger = some name →
      program.externals name = some foreign → foreign.signature = Logging.signature name →
      literals "logStatus" = some category → heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (CCalls.Events.machine program).Behaves start behavior ↔
      (∃ events value final, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value final ∧
        behavior = .terminates events ⟨.integer 3, final⟩) ∨
      ((∀ events value final, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value final) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program start heap p message category logger text name environment old foreign path
    helper literal address external prototype categoryBound mode loggerValue loggingValue environmentValue
  obtain ⟨env, types, code, reached, unshadowed, instanceBound⟩ := path
  have result := statement_all_behaviors context program env types code text heap p message category logger
    environment old name foreign unshadowed instanceBound helper literal address external prototype categoryBound
    mode loggerValue loggingValue environmentValue
  intro behavior
  exact (reached.silent_finite_behaviors (by intro history; simp [result]) behavior).trans (result behavior)

/-- Compose a prefix proved directly in the target interface with every
represented error callback outcome. -/
theorem prefix_all_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message category logger : Address)
      (text name : String) (environment : Option Address) (old : Option Value)
      (foreign : CCalls.Events.External E),
      @GuardedCalls.FailurePrefix context.target fn args before p text after →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message → program.addresses logger = some name →
      program.externals name = some foreign → foreign.signature = Logging.signature name →
      literals "logStatus" = some category →
      after (p.member "mode") = some ⟨.int32, true, old⟩ →
      load after (p.member "logger") = some (.pointer (some logger)) →
      load after (p.member "logging") = some (.integer 1) →
      load after (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      (∃ events value final, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode after p .terminated) events value final ∧
        behavior = .terminates events ⟨.integer 3, final⟩) ∨
      ((∀ events value final, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode after p .terminated) events value final) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program fn args before after p message category logger text name environment old foreign
    certified defined helper messageBound address external prototype literal hm hl hg he behavior
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ :=
    certified
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program fn args env later before after
    (Runtime.fail text :: tail) .done steps defined bound closed executed
  rw [status] at reached
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact statement_all_behaviors context program later types tail text after p message category logger
    environment old name foreign unshadowed instanceBound helper messageBound address external
    prototype literal hm hl hg he behavior

/-- A proved target-interface prefix followed by suppressed logging has
one complete Error/Terminated result. -/
theorem prefix_suppressed_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message : Address) (text : String)
      (old : Option Value) (logger : Option Address) (logging : Bool),
      @GuardedCalls.FailurePrefix context.target fn args before p text after →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      after (p.member "mode") = some ⟨.int32, true, old⟩ →
      load after (p.member "logger") = some (.pointer logger) →
      load after (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode after p .terminated⟩ := by
  letI : CInterface := context.target
  intro program fn args before after p message text old logger logging
    certified defined helper messageBound hm hl hg suppressed behavior
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ :=
    certified
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program fn args env later before after
    (Runtime.fail text :: tail) .done steps defined bound closed executed
  rw [status] at reached
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact statement_suppressed_behaviors context program later types tail text after p message old logger logging
    unshadowed instanceBound helper messageBound hm hl hg suppressed behavior

/-- The complete public failure path, including all callback outcomes. Its
guard prefix and helper are the actual function definitions, not postulated
successful API or logger calls. -/
theorem failure_all_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message category logger : Address)
      (text name : String) (environment : Option Address) (old : Option Value)
      (foreign : CCalls.Events.External E),
      CodeAgrees (cInterface literals) context.target fn.body →
      @GuardedCalls.FailurePrefix (cInterface literals) fn args before p text after →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message → program.addresses logger = some name →
      program.externals name = some foreign → foreign.signature = Logging.signature name →
      literals "logStatus" = some category →
      after (p.member "mode") = some ⟨.int32, true, old⟩ →
      load after (p.member "logger") = some (.pointer (some logger)) →
      load after (p.member "logging") = some (.integer 1) →
      load after (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      (∃ events value final, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode after p .terminated) events value final ∧
        behavior = .terminates events ⟨.integer 3, final⟩) ∨
      ((∀ events value final, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode after p .terminated) events value final) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program fn args before after p message category logger text name environment old foreign
    agrees certified defined helper messageBound address external prototype literal hm hl hg he behavior
  exact prefix_all_behaviors context program fn args before after p message category logger
    text name environment old foreign
    (failure_prefix context fn args before after p text agrees certified) defined helper messageBound
    address external prototype literal hm hl hg he behavior

theorem failure_suppressed_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message : Address) (text : String)
      (old : Option Value) (logger : Option Address) (logging : Bool),
      CodeAgrees (cInterface literals) context.target fn.body →
      @GuardedCalls.FailurePrefix (cInterface literals) fn args before p text after →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      after (p.member "mode") = some ⟨.int32, true, old⟩ →
      load after (p.member "logger") = some (.pointer logger) →
      load after (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode after p .terminated⟩ := by
  letI : CInterface := context.target
  intro program fn args before after p message text old logger logging
    agrees certified defined helper messageBound hm hl hg suppressed behavior
  exact prefix_suppressed_behaviors context program fn args before after p message text old logger logging
    (failure_prefix context fn args before after p text agrees certified) defined helper messageBound
    hm hl hg suppressed behavior

theorem failure_silent_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message : Address) (text : String)
      (old : Option Value) (logger : Option Address),
      CodeAgrees (cInterface literals) context.target fn.body →
      @GuardedCalls.FailurePrefix (cInterface literals) fn args before p text after →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      after (p.member "mode") = some ⟨.int32, true, old⟩ →
      load after (p.member "logger") = some (.pointer logger) →
      load after (p.member "logging") = some (.integer 0) → ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode after p .terminated⟩ := by
  letI : CInterface := context.target
  intro program fn args before after p message text old logger agrees certified defined helper messageBound hm hl hg behavior
  exact failure_suppressed_behaviors context program fn args before after p message text old logger false
    agrees certified defined helper messageBound hm hl hg (Or.inr rfl) behavior

theorem helper_missing_reaches {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (old : Option Value) (stack : CCalls.Typed.Continuation),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer none) →
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fail" [.pointer (some p), .pointer (some message)] heap stack)
        (.returning (.integer 3) (LifecycleBodies.writeMode heap p .terminated) stack) := by
  letI : CInterface := context.target
  intro program heap p message old stack defined hm hl
  have pure := ErrorBodies.failure_missing_run (static := ⟨literals⟩)
    (ErrorCalls.failureEnv p message) heap p old
    (by simp [ErrorCalls.failureEnv, CBody.bind, resolve]) hm hl
    (by simp [ErrorCalls.failureEnv, CBody.bind, resolve, constants])
  have transferred := (body_run_agreement (cInterface literals) context.target
    context.types context.bytes 3
    (.running Runtime.helpers[0].body (ErrorCalls.failureEnv p message) heap)
    (helper_agrees context)).symm.trans pure
  exact CCalls.Events.body_call_reaches program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] (ErrorCalls.failureEnv p message) heap
    ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ (.integer 3) stack 3 defined
    (helper_parameters context p message)
    (BodyEmbedding.helpers_closed _ (by simp [Runtime.helpers])) transferred context.error_cast

theorem statement_missing_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (env : Locals) (types : CLoops.Types)
      (code : List Stmt) (text : String) (heap : Heap) (p message : Address)
      (old : Option Value),
      env "fail" = none → resolve env "m" = some (.pointer (some p)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer none) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := context.target
  intro program env types code text heap p message old unshadowed instanceBound helper messageBound hm hl behavior
  let saved := CCalls.Typed.Continuation.caller .ret code env types "fmi3Status" .done
  have dispatched := helper_missing_reaches context program heap p message old saved helper hm hl
  have path := Transition.Reaches.next (step := fun s t => CCalls.Events.internalNext program s = some t)
    (statement_entry context program env types code text heap p message .done
      unshadowed instanceBound messageBound) dispatched
  exact (CCalls.Events.internal_prefix program path
    (CCalls.Events.internal_prefix program (.next
      (by simp [CCalls.Events.internalNext, CCalls.Typed.nextWith,
        CCalls.Typed.resume, saved, context.error_cast]) (.refl _))
      (CCalls.Events.return_forced program (.integer 3) (LifecycleBodies.writeMode heap p .terminated)))).behaviors behavior

theorem prefix_missing_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message : Address) (text : String) (old : Option Value),
      @GuardedCalls.FailurePrefix context.target fn args before p text after →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      after (p.member "mode") = some ⟨.int32, true, old⟩ →
      load after (p.member "logger") = some (.pointer none) → ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode after p .terminated⟩ := by
  letI : CInterface := context.target
  intro program fn args before after p message text old certified defined helper messageBound hm hl behavior
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ := certified
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program fn args env later before after
    (Runtime.fail text :: tail) .done steps defined bound closed executed
  rw [status] at reached
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact statement_missing_behaviors context program later types tail text after p message old
    unshadowed instanceBound helper messageBound hm hl behavior

theorem path_missing_behaviors {E : Type} (context : ErrorContext literals) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (start : CCalls.Typed.State) (heap : Heap)
      (p message : Address) (text : String) (old : Option Value),
      FailurePath program start heap p text →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer none) → ∀ behavior,
      (CCalls.Events.machine program).Behaves start behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := context.target
  intro program start heap p message text old path helper literal mode loggerValue
  obtain ⟨env, types, code, reached, unshadowed, instanceBound⟩ := path
  have result := statement_missing_behaviors context program env types code text heap p message old
    unshadowed instanceBound helper literal mode loggerValue
  intro behavior
  exact (reached.silent_finite_behaviors (by intro history; simp [result]) behavior).trans (result behavior)

end Rumoca.FMI3.StaticErrors
