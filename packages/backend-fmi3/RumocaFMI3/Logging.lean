import RumocaFMI3.ErrorCalls
import RumocaC.CallEvents

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
  apply CCalls.Events.internal_prefix program (.next
    (CCalls.Events.tree_entry program "fail" _ heap stack Runtime.helpers[0] env types defined
      (ErrorCalls.failure_parameters p message) boundTypes)
    (CCalls.Events.body_reaches program (CLoops.run_reaches dispatched') "fmi3Status" stack))
  let saved := CCalls.Typed.Continuation.caller .discard
    [Runtime.ret (Runtime.v "fmi3Error")] env types' "fmi3Status" stack
  have loggerAfter : load (writeMode heap p .terminated) (p.member "logger") =
      some (.pointer (some logger)) := by
    simpa only [load, write_frame heap p (p.member "logger") .terminated (by simp)] using hl
  have resolved : CCalls.Events.resolve program env (writeMode heap p .terminated) (Runtime.field "logger") =
      some name := by
    simp [CCalls.Events.resolve, CCalls.Indirect.resolve, Runtime.field, Runtime.v,
      CBody.eval, hp, Value.address, loggerAfter, CCalls.Indirect.valueTarget, address]
  have values := ErrorBodies.failure_log_arguments env heap p environment category message
    literal hp he errorValue messageValue
  have entered : CCalls.Events.internalNext program
      (.body (.running (ErrorBodies.logCall :: [Runtime.ret (Runtime.v "fmi3Error")])
        env types' (writeMode heap p .terminated)) "fmi3Status" stack) =
      some (.calling name (arguments environment category message) (writeMode heap p .terminated) saved) := by
    have blocked : CLoops.next (.running
        (ErrorBodies.logCall :: [Runtime.ret (Runtime.v "fmi3Error")]) env types'
        (writeMode heap p .terminated)) = none := by
      simp [CLoops.next, CLoops.eval, ErrorBodies.logCall, Runtime.field, Runtime.v, CBody.eval]
    simp only [CCalls.Events.internalNext, CCalls.Typed.nextWith, blocked]
    simp [CCalls.Events.enterCall, ErrorBodies.logCall, CCalls.Indirect.operand,
      resolved, values, arguments, saved]

  apply CCalls.Events.internal_prefix program (.next entered (.refl _))
  apply CCalls.Events.external_prefix program external (prototype ▸ arguments_converted name environment category message)
    executed unique
  apply CCalls.Events.internal_prefix program (t := .returning (.integer 3) after stack) _ rest
  refine .next (t := .body (.running [Runtime.ret (Runtime.v "fmi3Error")] env types' after)
    "fmi3Status" stack) (by rfl) ?_
  refine .next (t := .body (.returned ⟨.integer 3, after⟩) "fmi3Status" stack) ?_ ?_
  · simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
      Runtime.ret, Runtime.v, CBody.eval, errorValue]
  · exact .next (by rfl) (.refl _)

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
