import RumocaFMI3.StaticInitialization
import RumocaFMI3.GuardedCalls

/-! Complete failure-helper calls in the same object interface as static
creation. Existing pure prefix proofs are transferred by local lookup
agreement; callbacks keep every represented outcome and memory effect. -/
noncomputable section
namespace Rumoca.FMI3.StaticErrors
open CTree CMemory CBody StaticFactory CLiteral.Interface

/-- The nullable callback and Boolean flag exhaust the represented logging
domain. Missing callback support is handled defensively by the emitted guard. -/
theorem logging_cases (logger : Option Address) (logging : Bool) :
    (logger = none ∨ logging = false) ∨ ∃ address, logger = some address ∧ logging = true := by
  cases logger <;> cases logging <;> simp

theorem helper_agrees (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals) Runtime.helpers[0].body := by
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.helpers,
    Runtime.setMode, Runtime.put, Runtime.mode, Runtime.log, Runtime.branch,
    Runtime.ret, Runtime.v, Runtime.n, Runtime.field, Runtime.both,
    executionInterface, objectConstants]

theorem helper_parameters (objects : Objects) (literals : CLiteralAddresses)
    (p message : Address) :
    @CCalls.parameters (executionInterface objects literals) Runtime.helpers[0].signature.parameters
      [.pointer (some p), .pointer (some message)] = some (ErrorCalls.failureEnv p message) :=
  (parameters_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) _ _).symm.trans
    (ErrorCalls.failure_parameters (static := ⟨literals⟩) p message)

/-- Entry and the mode/logging guard reach the actual indirect callback site.
The callback itself has not been executed by this finite internal prefix. -/
theorem dispatch_reaches {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
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
  letI : CInterface := executionInterface objects literals
  intro program heap p message category logger environment old name stack defined address literal hm hl hg he
  let env := ErrorCalls.failureEnv p message
  have pure := ErrorBodies.failure_dispatch_run (static := ⟨literals⟩) env heap p old (some logger) true
    (by simp [env, ErrorCalls.failureEnv, CBody.bind, resolve]) hm hl hg
  simp only [Option.isSome_some, Bool.and_self, ↓reduceIte] at pure
  have transferred := (body_run_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) rfl 2
    (.running Runtime.helpers[0].body env heap) (helper_agrees objects literals)).symm.trans pure
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] env env heap
    (LifecycleBodies.writeMode heap p .terminated)
    [ErrorBodies.logCall, Runtime.ret (Runtime.v "fmi3Error")] stack 2 defined
    (helper_parameters objects literals p message)
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
  have errorBound : CInterface.constants "fmi3Error" = some (.integer 3) := rfl
  have categoryBound : CInterface.literals "logStatus" = some category := literal
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

theorem resume_reaches {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (p message : Address) (types : CLoops.Types)
      (stack : CCalls.Typed.Continuation) (value : Value) (heap : Heap),
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.returning value heap (Logging.failureContinuation p message types stack))
        (.returning (.integer 3) heap stack) := by
  letI : CInterface := executionInterface objects literals
  intro program p message types stack value heap
  let env := ErrorCalls.failureEnv p message
  have errorValue : resolve env "fmi3Error" = some (.integer 3) := by
    simp [env, ErrorCalls.failureEnv, CBody.bind, resolve, constants]
    rfl
  refine .next (t := .body (.running [Runtime.ret (Runtime.v "fmi3Error")] env types heap)
    "fmi3Status" stack) (by rfl) ?_
  refine .next (t := .body (.returned ⟨.integer 3, heap⟩) "fmi3Status" stack) ?_ ?_
  · simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
      Runtime.ret, Runtime.v, CBody.eval, errorValue]
  · exact .next (by rfl) (.refl _)

/-- All enabled callback outcomes, including an absent outcome, are retained.
This does not model the native callback's internal execution or reentry. -/
theorem helper_all_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
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
  letI : CInterface := executionInterface objects literals
  intro program heap p message category logger environment old name foreign
    defined address external prototype literal hm hl hg he behavior
  obtain ⟨types, dispatched⟩ := dispatch_reaches objects literals program heap p message category logger
    environment old name .done defined address literal hm hl hg he
  rw [CCalls.Events.internal_prefix_behaviors program dispatched behavior]
  apply CCalls.Events.external_choices_behaviors program external
    (prototype ▸ (show CCalls.Events.convertedArguments (Logging.signature name).parameters
      (Logging.arguments environment category message) = some (Logging.arguments environment category message) from rfl))
    (fun _ after => ⟨.integer 3, after⟩)
  intro events value after executed
  exact CCalls.Events.internal_prefix program
    (resume_reaches objects literals program p message types .done value after)
    (CCalls.Events.return_forced program (.integer 3) after)

theorem helper_suppressed_reaches {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
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
  letI : CInterface := executionInterface objects literals
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
  have transferred := (body_run_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) rfl 3
    (.running Runtime.helpers[0].body (ErrorCalls.failureEnv p message) heap)
    (helper_agrees objects literals)).symm.trans pure
  exact CCalls.Events.body_call_reaches program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] (ErrorCalls.failureEnv p message) heap
    ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ (.integer 3) stack 3 defined
    (helper_parameters objects literals p message)
    (BodyEmbedding.helpers_closed _ (by simp [Runtime.helpers])) transferred rfl

theorem helper_silent_reaches {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (old : Option Value) (logger : Option Address) (stack : CCalls.Typed.Continuation),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (.integer 0) →
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fail" [.pointer (some p), .pointer (some message)] heap stack)
        (.returning (.integer 3) (LifecycleBodies.writeMode heap p .terminated) stack) := by
  letI : CInterface := executionInterface objects literals
  intro program heap p message old logger stack defined hm hl hg
  exact helper_suppressed_reaches objects literals program heap p message old logger false stack
    defined hm hl hg (Or.inr rfl)

theorem helper_silent_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (old : Option Value) (logger : Option Address),
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (.integer 0) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling "fail" [.pointer (some p), .pointer (some message)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p message old logger defined hm hl hg behavior
  exact (CCalls.Events.internal_prefix program
    (helper_silent_reaches objects literals program heap p message old logger .done defined hm hl hg)
    (CCalls.Events.return_forced program (.integer 3) (LifecycleBodies.writeMode heap p .terminated))).behaviors behavior

/-- Prefix transport needs agreement only for the current function, including
its failure statement. It imposes no condition on unrelated factory bodies. -/
theorem failure_prefix (objects : Objects) (literals : CLiteralAddresses)
    (fn : Function) (args : List Value) (before after : Heap) (p : Address) (text : String)
    (agrees : CodeAgrees (cInterface literals) (executionInterface objects literals) fn.body)
    (certified : @GuardedCalls.FailurePrefix (cInterface literals) fn args before p text after) :
    @GuardedCalls.FailurePrefix (executionInterface objects literals) fn args before p text after := by
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ := certified
  refine ⟨status, closed, env, later, tail, steps, ?_, ?_, unshadowed, ?_⟩
  · exact (parameters_agreement (cInterface literals) (executionInterface objects literals)
      (StaticInitialization.interface_types objects literals) _ _).symm.trans bound
  · exact (body_run_agreement (cInterface literals) (executionInterface objects literals)
      (StaticInitialization.interface_types objects literals) rfl steps (.running fn.body env before) agrees).symm.trans executed
  · exact instanceBound

theorem statement_entry {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (env : Locals) (types : CLoops.Types)
      (code : List Stmt) (text : String) (heap : Heap) (p message : Address)
      (stack : CCalls.Typed.Continuation),
      env "fail" = none → resolve env "m" = some (.pointer (some p)) →
      literals text = some message →
      CCalls.Events.internalNext program
        (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" stack) =
      some (.calling "fail" [.pointer (some p), .pointer (some message)] heap
        (.caller .ret code env types "fmi3Status" stack)) := by
  letI : CInterface := executionInterface objects literals
  intro program env types code text heap p message stack unshadowed instanceBound messageBound
  have named : CInterface.constants "fail" = none := rfl
  have literal : CInterface.literals text = some message := messageBound
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

/-- The complete public failure path, including all callback outcomes. Its
guard prefix and helper are the actual function definitions, not postulated
successful API or logger calls. -/
theorem failure_all_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message category logger : Address)
      (text name : String) (environment : Option Address) (old : Option Value)
      (foreign : CCalls.Events.External E),
      CodeAgrees (cInterface literals) (executionInterface objects literals) fn.body →
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
  letI : CInterface := executionInterface objects literals
  intro program fn args before after p message category logger text name environment old foreign
    agrees certified defined helper messageBound address external prototype literal hm hl hg he behavior
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ :=
    failure_prefix objects literals fn args before after p text agrees certified
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program fn args env later before after
    (Runtime.fail text :: tail) .done steps defined bound closed executed
  rw [status] at reached
  let saved := CCalls.Typed.Continuation.caller .ret tail later types "fmi3Status" .done
  obtain ⟨helperTypes, dispatched⟩ := dispatch_reaches objects literals program after p message category logger
    environment old name saved helper address literal hm hl hg he
  have path := reached.trans (.next
    (statement_entry objects literals program later types tail text after p message .done
      unshadowed instanceBound messageBound) dispatched)
  rw [CCalls.Events.internal_prefix_behaviors program path behavior]
  apply CCalls.Events.external_choices_behaviors program external
    (prototype ▸ (show CCalls.Events.convertedArguments (Logging.signature name).parameters
      (Logging.arguments environment category message) = some (Logging.arguments environment category message) from rfl))
    (fun _ final => ⟨.integer 3, final⟩)
  intro events value final callback
  apply CCalls.Events.internal_prefix program
    (resume_reaches objects literals program p message helperTypes saved value final)
  exact CCalls.Events.internal_prefix program (.next (by rfl) (.refl _))
    (CCalls.Events.return_forced program (.integer 3) final)

theorem failure_suppressed_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message : Address) (text : String)
      (old : Option Value) (logger : Option Address) (logging : Bool),
      CodeAgrees (cInterface literals) (executionInterface objects literals) fn.body →
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
  letI : CInterface := executionInterface objects literals
  intro program fn args before after p message text old logger logging
    agrees certified defined helper messageBound hm hl hg suppressed behavior
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ :=
    failure_prefix objects literals fn args before after p text agrees certified
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program fn args env later before after
    (Runtime.fail text :: tail) .done steps defined bound closed executed
  rw [status] at reached
  let saved := CCalls.Typed.Continuation.caller .ret tail later types "fmi3Status" .done
  have dispatched := helper_suppressed_reaches objects literals program after p message old logger logging saved helper hm hl hg suppressed
  have path := reached.trans (.next
    (statement_entry objects literals program later types tail text after p message .done
      unshadowed instanceBound messageBound) dispatched)
  exact (CCalls.Events.internal_prefix program path
    (CCalls.Events.internal_prefix program (.next (by rfl) (.refl _))
      (CCalls.Events.return_forced program (.integer 3) (LifecycleBodies.writeMode after p .terminated)))).behaviors behavior

theorem failure_silent_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (fn : Function) (args : List Value)
      (before after : Heap) (p message : Address) (text : String)
      (old : Option Value) (logger : Option Address),
      CodeAgrees (cInterface literals) (executionInterface objects literals) fn.body →
      @GuardedCalls.FailurePrefix (cInterface literals) fn args before p text after →
      program.internal.definitions fn.signature.name = some (.tree fn) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals text = some message →
      after (p.member "mode") = some ⟨.int32, true, old⟩ →
      load after (p.member "logger") = some (.pointer logger) →
      load after (p.member "logging") = some (.integer 0) → ∀ behavior,
      (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode after p .terminated⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program fn args before after p message text old logger agrees certified defined helper messageBound hm hl hg behavior
  exact failure_suppressed_behaviors objects literals program fn args before after p message text old logger false
    agrees certified defined helper messageBound hm hl hg (Or.inr rfl) behavior

end Rumoca.FMI3.StaticErrors
