import RumocaFMI3.LoggingStatements
import RumocaFMI3.ErrorCalls

noncomputable section
namespace Rumoca.FMI3.GuardedCalls
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

theorem rejected_prefix (program : CCalls.Events.Program E) (fn : Function)
    (cmd : Command) (tail : List Stmt) (args : List Value) (env : Locals)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (parameters : CCalls.parameters fn.signature.parameters args = some env)
    (body : fn.body = Runtime.require cmd ++ tail)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (rejected : ¬ Reference.Allowed cmd kind mode) :
    ∃ types, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling fn.signature.name args heap stack)
      (.body (.running (Runtime.fail ErrorCalls.rejectionMessage :: tail)
        (CBody.bind env "m" (.pointer (some p))) types heap) fn.signature.result stack) := by
  have executed := LifecycleGuard.reject_prefix env heap p cmd kind mode tail hi hn hk hm rejected
  rw [← body] at executed
  exact CCalls.Events.body_prefix_reaches program fn args env _ heap heap _ stack 3
    defined parameters closed executed

theorem rejected_all_behaviors (program : CCalls.Events.Program E) (fn : Function)
    (cmd : Command) (tail : List Stmt) (args : List Value) (env : Locals)
    (heap : Heap) (p message category logger : Address) (environment : Option Address)
    (kind : Kind) (mode : Mode) (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (parameters : CCalls.parameters fn.signature.parameters args = some env)
    (body : fn.body = Runtime.require cmd ++ tail)
    (status : fn.signature.result = "fmi3Status")
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (unshadowed : env "fail" = none)
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (literal : static.addresses "logStatus" = some category)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment))
    (rejected : ¬ Reference.Allowed cmd kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling fn.signature.name args heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨types, reached⟩ := rejected_prefix program fn cmd tail args env heap p kind mode .done
    defined parameters body closed hi hn hk modeLoaded rejected
  rw [status] at reached
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Logging.failure_statement_all_behaviors program (CBody.bind env "m" (.pointer (some p))) types
    tail ErrorCalls.rejectionMessage heap p message category logger environment _ name foreign helper
    (by simp [CBody.bind, unshadowed]) (by simp [CBody.bind, resolve])
    messageBound address external prototype literal hm hl hg he behavior

theorem rejected_silent_behaviors (program : CCalls.Events.Program E) (fn : Function)
    (cmd : Command) (tail : List Stmt) (args : List Value) (env : Locals)
    (heap : Heap) (p message : Address) (logger : Option Address) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (parameters : CCalls.parameters fn.signature.parameters args = some env)
    (body : fn.body = Runtime.require cmd ++ tail)
    (status : fn.signature.result = "fmi3Status")
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (unshadowed : env "fail" = none)
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (rejected : ¬ Reference.Allowed cmd kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling fn.signature.name args heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨types, reached⟩ := rejected_prefix program fn cmd tail args env heap p kind mode .done
    defined parameters body closed hi hn hk modeLoaded rejected
  rw [status] at reached
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Logging.failure_statement_silent_behaviors program (CBody.bind env "m" (.pointer (some p))) types
    tail ErrorCalls.rejectionMessage heap p message _ logger helper
    (by simp [CBody.bind, unshadowed]) (by simp [CBody.bind, resolve]) messageBound hm hl hg behavior

/-- A disallowed public call with no logger returns Error without requiring a
readable logging flag or callback environment. -/
theorem rejected_missing_behaviors (program : CCalls.Events.Program E) (fn : Function)
    (cmd : Command) (tail : List Stmt) (args : List Value) (env : Locals)
    (heap : Heap) (p message : Address) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (parameters : CCalls.parameters fn.signature.parameters args = some env)
    (body : fn.body = Runtime.require cmd ++ tail)
    (status : fn.signature.result = "fmi3Status")
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (unshadowed : env "fail" = none)
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer none))
    (rejected : ¬ Reference.Allowed cmd kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling fn.signature.name args heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  obtain ⟨types, reached⟩ := rejected_prefix program fn cmd tail args env heap p kind mode .done
    defined parameters body closed hi hn hk modeLoaded rejected
  rw [status] at reached
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Logging.failure_statement_missing_behaviors program (CBody.bind env "m" (.pointer (some p))) types
    tail ErrorCalls.rejectionMessage heap p message _ helper
    (by simp [CBody.bind, unshadowed]) (by simp [CBody.bind, resolve]) messageBound hm hl behavior

theorem null_body (env : Locals) (heap : Heap) (rest : List Stmt)
    (hi : env "instance" = some (.pointer none)) (hn : env "m" = none)
    (error : env "fmi3Error" = none) :
    run 3 (.running (Runtime.instancePrefix ++ rest) env heap) = some (.returned ⟨.integer 3, heap⟩) := by
  simp [run, next, eval, Runtime.instancePrefix, Runtime.branch, Runtime.ret,
    Runtime.v, CBody.bind, resolve, constants, CBody.cast,
    convert, Value.truth, boolean, hi, hn, error]

theorem null_behaviors (program : CCalls.Events.Program E) (fn : Function)
    (rest : List Stmt) (args : List Value) (env : Locals) (heap : Heap)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (parameters : CCalls.parameters fn.signature.parameters args = some env)
    (body : fn.body = Runtime.instancePrefix ++ rest)
    (status : fn.signature.result = "fmi3Status")
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (hi : env "instance" = some (.pointer none)) (hn : env "m" = none)
    (error : env "fmi3Error" = none) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling fn.signature.name args heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply CCalls.Events.body_call_behaviors program fn args env heap ⟨.integer 3, heap⟩ (.integer 3) 3
    defined parameters closed
  · rw [body]
    exact null_body env heap rest hi hn error
  · rw [status]
    rfl

end Rumoca.FMI3.GuardedCalls

namespace Rumoca.FMI3.GuardedCalls
open CTree CMemory CBody

/-- A proved finite prefix reaches the actual failure statement. The witness
contains parameter binding and body execution, so callers cannot substitute a
selected error result for the emitted function's behavior. -/
def FailurePrefix [interface : CInterface] (fn : Function) (args : List Value)
    (before : Heap) (p : Address) (text : String) (after : Heap) : Prop :=
  fn.signature.result = "fmi3Status" ∧ fn.body.all CBodyEmbedding.closedBlocks = true ∧
  ∃ (env later : Locals) (tail : List Stmt) (steps : Nat),
    CCalls.parameters fn.signature.parameters args = some env ∧
    run steps (.running fn.body env before) = some (.running (Runtime.fail text :: tail) later after) ∧
    later "fail" = none ∧ resolve later "m" = some (.pointer (some p))

section
variable [static : StaticLiterals]
private local instance failureInterface : CInterface := cInterface static.addresses

theorem FailurePrefix.all_behaviors (program : CCalls.Events.Program E)
    (fn : Function) (args : List Value) (before after : Heap) (p message category logger : Address)
    (text name : String) (environment : Option Address) (old : Option Value)
    (foreign : CCalls.Events.External E)
    (certified : FailurePrefix fn args before p text after)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses text = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (literal : static.addresses "logStatus" = some category)
    (hm : after (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load after (p.member "logger") = some (.pointer (some logger)))
    (hg : load after (p.member "logging") = some (.integer 1))
    (he : load after (p.member "environment") = some (.pointer environment)) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      (∃ events value final, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode after p .terminated) events value final ∧
        behavior = .terminates events ⟨.integer 3, final⟩) ∨
      ((∀ events value final, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode after p .terminated) events value final) ∧ behavior = .wrong []) := by
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ := certified
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program fn args env later before after
    (Runtime.fail text :: tail) .done steps defined bound closed executed
  rw [status] at reached
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Logging.failure_statement_all_behaviors program later types tail text after p message
    category logger environment old name foreign helper unshadowed instanceBound messageBound
    address external prototype literal hm hl hg he behavior

theorem FailurePrefix.silent_behaviors (program : CCalls.Events.Program E)
    (fn : Function) (args : List Value) (before after : Heap) (p message : Address)
    (text : String) (old : Option Value) (logger : Option Address)
    (certified : FailurePrefix fn args before p text after)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses text = some message)
    (hm : after (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load after (p.member "logger") = some (.pointer logger))
    (hg : load after (p.member "logging") = some (.integer 0)) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling fn.signature.name args before .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode after p .terminated⟩ := by
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ := certified
  obtain ⟨types, reached⟩ := CCalls.Events.body_prefix_reaches program fn args env later before after
    (Runtime.fail text :: tail) .done steps defined bound closed executed
  rw [status] at reached
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Logging.failure_statement_silent_behaviors program later types tail text after p message
    old logger helper unshadowed instanceBound messageBound hm hl hg behavior

end
end Rumoca.FMI3.GuardedCalls

namespace Rumoca.FMI3.GuardedCalls
open CTree CMemory CBody

/-- Any checked pure failure prefix preserves existing immutable objects. -/
theorem FailurePrefix.readonly [CInterface]
    (certified : GuardedCalls.FailurePrefix fn args before p text after) :
    CReadOnly.Preserves before after := by
  obtain ⟨_, _, env, later, tail, steps, _, executed, _, _⟩ := certified
  exact CReadOnly.body_reaches (CBody.run_reaches executed)

/-- Prefix execution and the required mode write derive the read-only frame at
the callback entry. No callback frame or post-callback property is asserted. -/
theorem FailurePrefix.error_readonly [CInterface]
    (certified : GuardedCalls.FailurePrefix fn args before p text after)
    (old : Option Value)
    (writable : after (p.member "mode") = some ⟨.int32, true, old⟩) :
    CReadOnly.Preserves before (LifecycleBodies.writeMode after p .terminated) :=
  certified.readonly.trans (LifecycleBodies.writeMode_readonly after p .terminated old writable)

end Rumoca.FMI3.GuardedCalls
