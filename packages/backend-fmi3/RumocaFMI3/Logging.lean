import RumocaFMI3.ErrorCalls
import RumocaC.CallEventChoices
import RumocaC.BodyEvents

/-! Complete execution of the emitted failure helper with enabled logging.
The foreign function's signature, return and memory effects are explicit host
contracts. This module proves calls in the authored symbolic C semantics;
native function-pointer layout and ABI are separate obligations. -/
noncomputable section
namespace Rumoca.FMI3.Logging
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody LifecycleBodies

/-- The pinned FMI callback prototype, with an importer-owned symbol name. -/
def signature (name : String) : Signature :=
  ⟨"void", name, [⟨"fmi3InstanceEnvironment", "instanceEnvironment", false⟩,
    ⟨"fmi3Status", "status", false⟩, ⟨"fmi3String", "category", false⟩,
    ⟨"fmi3String", "message", false⟩]⟩

def arguments (environment : Option Address) (category message : Address) : List Value :=
  [.pointer environment, .integer 3, .pointer (some category), .pointer (some message)]

theorem arguments_converted (name : String) (environment : Option Address)
    (category message : Address) :
    CCalls.Events.convertedArguments (signature name).parameters (arguments environment category message) =
      some (arguments environment category message) := by
  rfl

def failureContinuation (p message : Address) (types : CLoops.Types) (stack : CCalls.Typed.Continuation) :
    CCalls.Typed.Continuation :=
  .caller .discard [Runtime.ret (Runtime.v "fmi3Error")]
    (ErrorCalls.failureEnv p message) types "fmi3Status" stack

theorem failure_dispatch_reaches (program : CCalls.Events.Program E)
    (heap : Heap) (p message category logger : Address) (environment : Option Address)
    (old : Option Value) (name : String) (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (address : program.addresses logger = some name)
    (literal : static.addresses "logStatus" = some category)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment)) :
    ∃ types, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fail" [.pointer (some p), .pointer (some message)] heap stack)
      (.calling name (arguments environment category message) (writeMode heap p .terminated)
        (failureContinuation p message types stack)) := by
  let env := ErrorCalls.failureEnv p message
  have hp : resolve env "m" = some (.pointer (some p)) := by
    simp [env, ErrorCalls.failureEnv, CBody.bind, resolve]
  have errorValue : resolve env "fmi3Error" = some (.integer 3) := by
    simp [env, ErrorCalls.failureEnv, CBody.bind, resolve, constants]
  have messageValue : resolve env "message" = some (.pointer (some message)) := by
    simp [env, ErrorCalls.failureEnv, CBody.bind, resolve]
  obtain ⟨types, boundTypes, _⟩ := CCalls.Parameters.parameters_typed _ _ _
    (ErrorCalls.failure_parameters p message)
  have dispatched := ErrorBodies.failure_dispatch_run env heap p old (some logger) true hp hm hl hg
  simp only [Option.isSome_some, Bool.and_self, ↓reduceIte] at dispatched
  obtain ⟨types', dispatched', _⟩ := CBodyEmbedding.run_refines 2
    (.running Runtime.helpers[0].body env heap) _ types
    (BodyEmbedding.helpers_closed Runtime.helpers[0] (by simp [Runtime.helpers])) dispatched
  have path := Transition.Reaches.next
    (step := fun s t => CCalls.Events.internalNext program s = some t)
    (CCalls.Events.tree_entry program "fail" _ heap stack Runtime.helpers[0] env types defined
      (ErrorCalls.failure_parameters p message) boundTypes)
    (CCalls.Events.body_reaches program (CLoops.run_reaches dispatched') "fmi3Status" stack)
  let saved := CCalls.Typed.Continuation.caller .discard
    [Runtime.ret (Runtime.v "fmi3Error")] env types' "fmi3Status" stack
  have loggerAfter : load (writeMode heap p .terminated) (p.member "logger") =
      some (.pointer (some logger)) := by
    simpa only [load, write_frame heap p (p.member "logger") .terminated (by simp)] using hl
  have resolved : CCalls.Events.resolve program env (writeMode heap p .terminated) (Runtime.field "logger") =
      some name := by
    simp [CCalls.Events.resolve, CCalls.Events.resolveWith, CCalls.Indirect.resolveWith, CBody.legacyExpressions, Runtime.field, Runtime.v,
      CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, hp, Value.address, loggerAfter, CCalls.Indirect.valueTarget, address]
  have values := ErrorBodies.failure_log_arguments env heap p environment category message
    literal hp he errorValue messageValue
  have entered : CCalls.Events.internalNext program
      (.body (.running (ErrorBodies.logCall :: [Runtime.ret (Runtime.v "fmi3Error")])
        env types' (writeMode heap p .terminated)) "fmi3Status" stack) =
      some (.calling name (arguments environment category message) (writeMode heap p .terminated) saved) := by
    have blocked : CLoops.next (.running
        (ErrorBodies.logCall :: [Runtime.ret (Runtime.v "fmi3Error")]) env types'
        (writeMode heap p .terminated)) = none := by
      simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, ErrorBodies.logCall, Runtime.field, Runtime.v, CBody.eval, CBody.evalWith]
    simp only [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, blocked]
    simp [CCalls.Events.enterCallWith, ErrorBodies.logCall, CCalls.Indirect.operand,
      resolved, values, arguments, saved]

  exact ⟨types', path.trans (.next entered (.refl _))⟩

theorem failure_resume_reaches (program : CCalls.Events.Program E)
    (p message : Address) (types : CLoops.Types) (stack : CCalls.Typed.Continuation)
    (value : Value) (heap : Heap) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.returning value heap (failureContinuation p message types stack))
      (.returning (.integer 3) heap stack) := by
  let env := ErrorCalls.failureEnv p message
  have errorValue : resolve env "fmi3Error" = some (.integer 3) := by
    simp [env, ErrorCalls.failureEnv, CBody.bind, resolve, constants]
  refine .next (t := .body (.running [Runtime.ret (Runtime.v "fmi3Error")] env types heap)
    "fmi3Status" stack) (by rfl) ?_
  refine .next (t := .body (.returned ⟨.integer 3, heap⟩) "fmi3Status" stack) ?_ ?_
  · simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
      Runtime.ret, Runtime.v, CBody.eval, CBody.evalWith, errorValue]
  · exact .next (by rfl) (.refl _)

/-- Every represented host outcome is retained. An absent outcome is accounted
for as stuck execution in this atomic external-call model. No chosen outcome
or callback determinacy is assumed. -/
theorem failure_all_behaviors (program : CCalls.Events.Program E)
    (heap : Heap) (p message category logger : Address) (environment : Option Address)
    (old : Option Value) (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = signature name)
    (literal : static.addresses "logStatus" = some category)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fail" [.pointer (some p), .pointer (some message)] heap .done) behavior ↔
      (∃ events value after, foreign.execute (arguments environment category message)
        (writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (arguments environment category message)
        (writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  obtain ⟨types, dispatched⟩ := failure_dispatch_reaches program heap p message category logger
    environment old name .done defined address literal hm hl hg he
  rw [CCalls.Events.internal_prefix_behaviors program dispatched behavior]
  apply CCalls.Events.external_choices_behaviors program external
    (prototype ▸ arguments_converted name environment category message)
    (fun _ after => ⟨.integer 3, after⟩)
  intro events value after executed
  exact CCalls.Events.internal_prefix program (failure_resume_reaches program p message types .done value after)
    (CCalls.Events.return_forced program (.integer 3) after)

/-- Disabled logging has no observable callback events, even if the program
binds a nondeterministic importer logger. The only write changes the mode. -/
theorem failure_silent_behaviors (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
    (old : Option Value) (logger : Option Address)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fail" [.pointer (some p), .pointer (some message)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, writeMode heap p .terminated⟩ := by
  apply CCalls.Events.body_call_behaviors program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] (ErrorCalls.failureEnv p message) heap
    ⟨.integer 3, writeMode heap p .terminated⟩ (.integer 3) 3 defined (ErrorCalls.failure_parameters p message)
    (BodyEmbedding.helpers_closed _ (by simp [Runtime.helpers]))
  · exact ErrorBodies.failure_silent_run _ heap p old logger
      (by simp [ErrorCalls.failureEnv, CBody.bind, resolve]) hm hl hg
      (by simp [ErrorCalls.failureEnv, CBody.bind, resolve, constants])
  · rfl

/-- The returning host contract is local to this invocation. Other foreign
calls may behave differently; callback effects on writable memory are retained
in `after`, rather than replaced with a no-op logger. -/
theorem failure_prefix {E : Type} (program : CCalls.Events.Program E)
    (heap after : Heap) (p message category logger : Address) (environment : Option Address)
    (old : Option Value) (name : String) (foreign : CCalls.Events.External E)
    (stack : CCalls.Typed.Continuation) (trace tail : List E) (final : CBody.Result)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = signature name)
    (literal : static.addresses "logStatus" = some category)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment))
    (executed : foreign.execute (arguments environment category message)
      (writeMode heap p .terminated) trace .void after)
    (unique : ∀ events value out, foreign.execute (arguments environment category message)
      (writeMode heap p .terminated) events value out →
      events = trace ∧ value = .void ∧ out = after)
    (rest : Transition.Events.Forced (CCalls.Events.machine program)
      (.returning (.integer 3) after stack) tail final) :
    Transition.Events.Forced (CCalls.Events.machine program)
      (.calling "fail" [.pointer (some p), .pointer (some message)] heap stack)
      (trace ++ tail) final := by
  obtain ⟨types, dispatched⟩ := failure_dispatch_reaches program heap p message category logger
    environment old name stack defined address literal hm hl hg he
  apply CCalls.Events.internal_prefix program dispatched
  apply CCalls.Events.external_prefix program external
    (prototype ▸ arguments_converted name environment category message) executed unique
  exact CCalls.Events.internal_prefix program
    (failure_resume_reaches program p message types stack .void after) rest

theorem failure_behaviors {E : Type} (program : CCalls.Events.Program E)
    (heap after : Heap) (p message category logger : Address) (environment : Option Address)
    (old : Option Value) (name : String) (foreign : CCalls.Events.External E) (trace : List E)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = signature name)
    (literal : static.addresses "logStatus" = some category)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment))
    (executed : foreign.execute (arguments environment category message)
      (writeMode heap p .terminated) trace .void after)
    (unique : ∀ events value out, foreign.execute (arguments environment category message)
      (writeMode heap p .terminated) events value out →
      events = trace ∧ value = .void ∧ out = after) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fail" [.pointer (some p), .pointer (some message)] heap .done) behavior ↔
      behavior = .terminates trace ⟨.integer 3, after⟩ := by
  apply Transition.Events.Forced.behaviors
  simpa only [List.append_nil] using failure_prefix program heap after p message category logger
    environment old name foreign .done trace [] ⟨.integer 3, after⟩ defined address external prototype
    literal hm hl hg he executed unique (CCalls.Events.return_forced program (.integer 3) after)

end Rumoca.FMI3.Logging
