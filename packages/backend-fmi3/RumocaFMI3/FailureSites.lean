import RumocaFMI3.LoggingStatements

/-! A common error continuation for prefixes containing typed loops or nested
internal calls. API proofs construct this witness from independent argument
conditions; a host never supplies a selected error execution as a premise. -/
noncomputable section
namespace Rumoca.FMI3.GuardedCalls
open CTree CMemory CBody

def FailureSite [interface : CInterface] (program : CCalls.Events.Program E)
    (start : CCalls.Typed.State) (heap : Heap) (p : Address) (text : String) : Prop :=
  ∃ (env : Locals) (types : CLoops.Types) (rest : List Stmt),
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t) start
      (.body (.running (Runtime.fail text :: rest) env types heap) "fmi3Status" .done) ∧
    env "fail" = none ∧ resolve env "m" = some (.pointer (some p))

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem FailureSite.all_behaviors (program : CCalls.Events.Program E)
    (start : CCalls.Typed.State) (heap : Heap) (p message category logger : Address)
    (text name : String) (environment : Option Address) (old : Option Value)
    (foreign : CCalls.Events.External E) (certified : FailureSite program start heap p text)
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses text = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (literal : static.addresses "logStatus" = some category)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer (some logger)))
    (hg : load heap (p.member "logging") = some (.integer 1))
    (he : load heap (p.member "environment") = some (.pointer environment)) (behavior) :
    (CCalls.Events.machine program).Behaves start behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  obtain ⟨env, types, rest, reached, unshadowed, instanceBound⟩ := certified
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Logging.failure_statement_all_behaviors program env types rest text heap p message
    category logger environment old name foreign helper unshadowed instanceBound messageBound
    address external prototype literal hm hl hg he behavior

theorem FailureSite.silent_behaviors (program : CCalls.Events.Program E)
    (start : CCalls.Typed.State) (heap : Heap) (p message : Address)
    (text : String) (old : Option Value) (logger : Option Address)
    (certified : FailureSite program start heap p text)
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses text = some message)
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) (behavior) :
    (CCalls.Events.machine program).Behaves start behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  obtain ⟨env, types, rest, reached, unshadowed, instanceBound⟩ := certified
  rw [CCalls.Events.internal_prefix_behaviors program reached behavior]
  exact Logging.failure_statement_silent_behaviors program env types rest text heap p message
    old logger helper unshadowed instanceBound messageBound hm hl hg behavior

end
end Rumoca.FMI3.GuardedCalls
