import RumocaFMI3.Logging

/-! Actual return-fail statements, including every callback outcome and disabled logging.
Public APIs supply their own independently proved guard prefixes. -/
noncomputable section
namespace Rumoca.FMI3.Logging
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody LifecycleBodies

theorem failure_statement_entry (program : CCalls.Events.Program E)
    (env : Locals) (types : CLoops.Types) (code : List Stmt) (text : String)
    (heap : Heap) (p message : Address) (stack : CCalls.Typed.Continuation)
    (unshadowed : env "fail" = none)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (messageBound : static.addresses text = some message) :
    CCalls.Events.internalNext program
      (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" stack) =
      some (.calling "fail" [.pointer (some p), .pointer (some message)] heap
        (.caller .ret code env types "fmi3Status" stack)) := by
  let saved := CCalls.Typed.Continuation.caller .ret code env types "fmi3Status" stack
  have resolved : CCalls.Events.resolve program env heap (Runtime.v "fail") = some "fail" := by
    simp [CCalls.Events.resolve, CCalls.Indirect.resolve, Runtime.v,
      resolve, unshadowed, constants]
  have values : CCalls.arguments env heap [Runtime.v "m", .str text] =
      some [.pointer (some p), .pointer (some message)] := by
    simp [CCalls.arguments, Runtime.v, CBody.eval, instanceBound, messageBound]
  have blocked : CLoops.next (.running (Runtime.fail text :: code) env types heap) = none := by
    simp [CLoops.next, CLoops.eval, Runtime.fail, Runtime.ret, Runtime.call, Runtime.v, CBody.eval]
  have entered : CCalls.Events.internalNext program
      (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" stack) =
      some (.calling "fail" [.pointer (some p), .pointer (some message)] heap saved) := by
    simp only [CCalls.Events.internalNext, CCalls.Typed.nextWith, blocked]
    simp only [CCalls.Events.enterCall, Runtime.fail, Runtime.ret, Runtime.call, CCalls.Indirect.operand]
    simp [resolved, values, saved]
  exact entered

theorem failure_statement_all_behaviors (program : CCalls.Events.Program E)
    (env : Locals) (types : CLoops.Types) (code : List Stmt) (text : String)
    (heap : Heap) (p message category logger : Address) (environment : Option Address)
    (old : Option Value) (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (unshadowed : env "fail" = none)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (messageBound : static.addresses text = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = signature name)
    (literal : static.addresses "logStatus" = some category)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" .done) behavior ↔
      (∃ events value after, foreign.execute (arguments environment category message)
        (writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (arguments environment category message)
        (writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  let saved := CCalls.Typed.Continuation.caller .ret code env types "fmi3Status" .done
  obtain ⟨helperTypes, dispatched⟩ := failure_dispatch_reaches program heap p message category logger
    environment old name saved defined address literal hm hl hg he
  have path := Transition.Reaches.next
    (step := fun s t => CCalls.Events.internalNext program s = some t)
    (failure_statement_entry program env types code text heap p message .done
      unshadowed instanceBound messageBound) dispatched
  rw [CCalls.Events.internal_prefix_behaviors program path behavior]
  apply CCalls.Events.external_choices_behaviors program external
    (prototype ▸ arguments_converted name environment category message) (fun _ after => ⟨.integer 3, after⟩)
  intro events value after executed
  apply CCalls.Events.internal_prefix program
    (failure_resume_reaches program p message helperTypes saved value after)
  apply CCalls.Events.internal_prefix program
    (t := .returning (.integer 3) after .done) (.next (by rfl) (.refl _))
  exact CCalls.Events.return_forced program (.integer 3) after

theorem failure_statement_silent_behaviors (program : CCalls.Events.Program E)
    (env : Locals) (types : CLoops.Types) (code : List Stmt) (text : String)
    (heap : Heap) (p message : Address) (old : Option Value) (logger : Option Address)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (unshadowed : env "fail" = none)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (messageBound : static.addresses text = some message)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, writeMode heap p .terminated⟩ := by
  let saved := CCalls.Typed.Continuation.caller .ret code env types "fmi3Status" .done
  apply Transition.Events.Forced.behaviors
  apply CCalls.Events.internal_prefix program (.next
    (failure_statement_entry program env types code text heap p message .done
      unshadowed instanceBound messageBound) (.refl _))
  apply CCalls.Events.body_call_prefix program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] (ErrorCalls.failureEnv p message) heap
    ⟨.integer 3, writeMode heap p .terminated⟩ (.integer 3) saved 3 defined
    (ErrorCalls.failure_parameters p message) (BodyEmbedding.helpers_closed _ (by simp [Runtime.helpers]))
  · exact ErrorBodies.failure_silent_run _ heap p old logger
      (by simp [ErrorCalls.failureEnv, CBody.bind, resolve]) hm hl hg
      (by simp [ErrorCalls.failureEnv, CBody.bind, resolve, constants])
  · rfl
  · exact CCalls.Events.internal_prefix program (.next (by rfl) (.refl _))
      (CCalls.Events.return_forced program (.integer 3) (writeMode heap p .terminated))

/-- A missing logger makes the complete failure call return Error without
reading the logging flag or invoking any foreign callback. -/
theorem failure_statement_missing_behaviors (program : CCalls.Events.Program E)
    (env : Locals) (types : CLoops.Types) (code : List Stmt) (text : String)
    (heap : Heap) (p message : Address) (old : Option Value)
    (defined : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (unshadowed : env "fail" = none)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (messageBound : static.addresses text = some message)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer none)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (Runtime.fail text :: code) env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, writeMode heap p .terminated⟩ := by
  let saved := CCalls.Typed.Continuation.caller .ret code env types "fmi3Status" .done
  apply Transition.Events.Forced.behaviors
  apply CCalls.Events.internal_prefix program (.next
    (failure_statement_entry program env types code text heap p message .done
      unshadowed instanceBound messageBound) (.refl _))
  apply CCalls.Events.body_call_prefix program Runtime.helpers[0]
    [.pointer (some p), .pointer (some message)] (ErrorCalls.failureEnv p message) heap
    ⟨.integer 3, writeMode heap p .terminated⟩ (.integer 3) saved 3 defined
    (ErrorCalls.failure_parameters p message) (BodyEmbedding.helpers_closed _ (by simp [Runtime.helpers]))
  · exact ErrorBodies.failure_missing_run _ heap p old
      (by simp [ErrorCalls.failureEnv, CBody.bind, resolve]) hm hl
      (by simp [ErrorCalls.failureEnv, CBody.bind, resolve, constants])
  · rfl
  · exact CCalls.Events.internal_prefix program (.next (by rfl) (.refl _))
      (CCalls.Events.return_forced program (.integer 3) (writeMode heap p .terminated))

end Rumoca.FMI3.Logging
