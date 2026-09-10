import RumocaFMI3.BodyEmbedding

/-! Rejected lifecycle calls and the actual failure helper. Disabled logging
has a complete body-entry result/frame theorem. Enabled logging reaches its
correct callback request; executing that foreign callback, binding string
arguments and certifying the printed adapter are still separate obligations. -/
namespace Rumoca.FMI3.ErrorBodies
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody LifecycleBodies

def logCall : Stmt := .eval (.call (Runtime.field "logger")
  [Runtime.field "environment", Runtime.v "fmi3Error", .str "logStatus", Runtime.v "message"])

/-- Both logging branches of the actual failure helper, through dispatch. -/
theorem failure_dispatch_run (env : Locals) (heap : Heap) (p : Address)
    (old : Option Value) (logger : Option Address) (logging : Bool)
    (hp : resolve env "m" = some (.pointer (some p)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (boolean logging)) :
    run 2 (.running Runtime.helpers[0].body env heap) =
      some (.running ((if logger.isSome && logging then [logCall] else []) ++
        [Runtime.ret (Runtime.v "fmi3Error")]) env (writeMode heap p .terminated)) := by
  have hl' : load (writeMode heap p .terminated) (p.member "logger") = some (.pointer logger) := by
    simpa only [load, write_frame heap p (p.member "logger") .terminated (by simp)] using hl
  have hg' : load (writeMode heap p .terminated) (p.member "logging") = some (boolean logging) := by
    simpa only [load, write_frame heap p (p.member "logging") .terminated (by simp)] using hg
  rw [show 2 = 1 + 1 from rfl, run_add, failure_mode_run env heap p old hp hm]
  cases logger <;> cases logging <;>
    simp [run, next, Runtime.log, Runtime.branch, Runtime.both,
      Runtime.field, Runtime.v, Runtime.ret, eval, hp, Value.address, hl', hg',
      Value.truth, boolean, logCall]

/-- The enabled request uses the actual environment, Error status, declared
category and message. This evaluates arguments, not the foreign callback. -/
theorem failure_log_arguments (env : Locals) (heap : Heap) (p : Address)
    (environment : Option Address) (category message : Address)
    (hc : static.addresses "logStatus" = some category)
    (hp : resolve env "m" = some (.pointer (some p)))
    (hv : load heap (p.member "environment") = some (.pointer environment))
    (he : resolve env "fmi3Error" = some (.integer 3))
    (hm : resolve env "message" = some (.pointer (some message))) :
    CCalls.arguments env (writeMode heap p .terminated)
      [Runtime.field "environment", Runtime.v "fmi3Error", .str "logStatus", Runtime.v "message"] =
        some [.pointer environment, .integer 3, .pointer (some category), .pointer (some message)] := by
  have hv' : load (writeMode heap p .terminated) (p.member "environment") = some (.pointer environment) := by
    simpa only [load, write_frame heap p (p.member "environment") .terminated (by simp)] using hv
  simp [CCalls.arguments, Runtime.field, Runtime.v, eval, hp, Value.address, hv', he, hm, hc]

/-- Execute the complete existing failure body when logging is disabled.
No callback behavior is assumed: its branch is not taken. -/
theorem failure_silent_run (env : Locals) (heap : Heap) (p : Address)
    (old : Option Value) (logger : Option Address)
    (hp : resolve env "m" = some (.pointer (some p)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (he : resolve env "fmi3Error" = some (.integer 3)) :
    run 3 (.running Runtime.helpers[0].body env heap) =
      some (.returned ⟨.integer 3, writeMode heap p .terminated⟩) := by
  rw [show 3 = 2 + 1 from rfl, run_add,
    failure_dispatch_run env heap p old logger false hp hm hl hg]
  simp [run, next, Runtime.ret, Runtime.v, eval, he]

/-- The rejected nominal query reaches the failure call before any output
access. No output-pointer validity is needed and the whole heap is unchanged.
This is a prefix theorem, not execution of the pending helper call. -/
theorem nominals_reject_run (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3GetNominalsOfContinuousStates")
    (env : Locals) (heap : Heap) (p : Address) (kind : Kind)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer Mode.instantiated.code)) :
    run 3 (.running (Runtime.body m sig) env heap) =
      some (.running ([Runtime.fail "Call is not allowed in the current FMI state"] ++
        Runtime.scalarAccessCheck "nominals" "nContinuousStates" ++
        [.assign (.index (Runtime.v "nominals") (Runtime.n 0)) (Runtime.n 1), Runtime.ok])
        (CBody.bind env "m" (.pointer (some p))) heap) := by
  simpa [Runtime.body, hsig, List.append_assoc] using
    LifecycleGuard.reject_prefix env heap p .getNominals kind .instantiated
      (Runtime.scalarAccessCheck "nominals" "nContinuousStates" ++
        [.assign (.index (Runtime.v "nominals") (Runtime.n 0)) (Runtime.n 1), Runtime.ok])
      hi hn hk hm (nominals_reject_instantiated kind)

noncomputable section
/-- Rejection reaches the same failure continuation in the typed call machine
used by tensor kernels, retaining all caller memory and the supplied stack. -/
theorem nominals_reject_reaches (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3GetNominalsOfContinuousStates")
    (program : CCalls.Program) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p : Address) (kind : Kind) (stack : CCalls.Typed.Continuation)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer Mode.instantiated.code)) :
    ∃ types', Transition.Reaches (CCalls.Typed.machine program).step
      (.body (.running (Runtime.body m sig) env types heap) "fmi3Status" stack)
      (.body (.running ([Runtime.fail "Call is not allowed in the current FMI state"] ++
        Runtime.scalarAccessCheck "nominals" "nContinuousStates" ++
        [.assign (.index (Runtime.v "nominals") (Runtime.n 0)) (Runtime.n 1), Runtime.ok])
        (CBody.bind env "m" (.pointer (some p))) types' heap) "fmi3Status" stack) := by
  obtain ⟨types', run, _⟩ := CBodyEmbedding.run_refines 3
    (.running (Runtime.body m sig) env heap) _ types
    (BodyEmbedding.body_closed m sig)
    (nominals_reject_run m sig hsig env heap p kind hi hn hk hm)
  exact ⟨types', CCalls.Typed.body_reaches program (CLoops.run_reaches run) "fmi3Status" stack⟩

/-- Body-entry behavior and whole-heap frame for disabled logging. The enabled
callback, string argument binding and actual printed function remain open. -/
theorem failure_silent_correct (program : CCalls.Program) (env : Locals)
    (types : CLoops.Types) (heap : Heap) (p : Address) (old : Option Value) (logger : Option Address)
    (hp : resolve env "m" = some (.pointer (some p)))
    (hm : heap (p.member "mode") = some ⟨.int32, true, old⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (he : resolve env "fmi3Error" = some (.integer 3)) :
    (∀ b, (CCalls.Typed.machine program).Behaves
      (.body (.running Runtime.helpers[0].body env types heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 3, writeMode heap p .terminated⟩) ∧
    (∀ q, q ≠ p.member "mode" → writeMode heap p .terminated q = heap q) := by
  exact ⟨fun b => CBodyEmbedding.typed_body_behaviors program
      (.running Runtime.helpers[0].body env heap) types
      ⟨.integer 3, writeMode heap p .terminated⟩ "fmi3Status" (.integer 3) 3
      (BodyEmbedding.helpers_closed Runtime.helpers[0] (by simp [Runtime.helpers]))
      (failure_silent_run env heap p old logger hp hm hl hg he)
      (by simp [CCalls.returnCast, CBody.cast, convert]) b,
    fun q hq => write_frame heap p q .terminated hq⟩
end
end Rumoca.FMI3.ErrorBodies
