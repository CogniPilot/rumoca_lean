import RumocaFMI3.CountQueries
import RumocaFMI3.GuardedCalls

namespace Rumoca.FMI3.CountQueries
open CTree CMemory CBody CLiteral LiteralPreparation

def failureMessage (missing : Bool) : String :=
  if missing then "Missing output pointer" else "Call is not allowed in the current FMI state"

def FailureCondition (missing : Bool) (kind : Kind) (mode : Mode) (buffer : Option Address) : Prop :=
  if missing then buffer = none ∧ Reference.Allowed .getCounts kind mode
  else ¬ Reference.Allowed .getCounts kind mode

theorem message_collected (m : Solve.FMI3Model source) (events missing : Bool) :
    failureMessage missing ∈ functionTexts (Runtime.function m (signature events)) := by
  cases events <;> cases missing <;>
    simp [Runtime.function, Runtime.body, signature, outputName, failureMessage,
      functionTexts, statementTexts, expressionTexts, Runtime.require,
      Runtime.instancePrefix, Runtime.pointerCheck, Runtime.reject, Runtime.branch,
      Runtime.fail, Runtime.ret, Runtime.call, Runtime.v]

noncomputable section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

/-- Bind the actual count-call arguments and reach its failure statement
before invoking the shared helper or any callback. -/
theorem failure_prefix (model : Solve.FMI3Model source) (events missing : Bool)
    (heap : Heap) (p : Address) (buffer : Option Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (condition : FailureCondition missing kind mode buffer) :
    GuardedCalls.FailurePrefix (Runtime.function model (signature events)) (arguments (some p) buffer)
      heap p (failureMessage missing) heap := by
  cases missing with
  | false =>
    refine ⟨by cases events <;> rfl, BodyEmbedding.body_closed model (signature events),
      parameters events (some p) buffer, CBody.bind (parameters events (some p) buffer) "m" (.pointer (some p)),
      rest events, 3, parameters_bound events (some p) buffer, ?_, ?_, ?_⟩
    · have executed := LifecycleGuard.reject_prefix (parameters events (some p) buffer) heap p
        .getCounts kind mode (rest events) (by simp [parameters, CBody.bind])
        (by cases events <;> simp [parameters, CBody.bind, outputName]) hk hm condition
      rw [← body_eq model events] at executed
      exact executed
    · cases events <;> simp [parameters, CBody.bind, outputName]
    · simp [CBody.bind, resolve]
  | true =>
    obtain ⟨rfl, allowed⟩ := condition
    refine ⟨by cases events <;> rfl, BodyEmbedding.body_closed model (signature events),
      parameters events (some p) none, CBody.bind (parameters events (some p) none) "m" (.pointer (some p)),
      [Runtime.out (outputName events) (Runtime.n (count events)), Runtime.ok], 4,
      parameters_bound events (some p) none, missing_run model events heap p kind mode hk hm allowed, ?_, ?_⟩
    · cases events <;> simp [parameters, CBody.bind, outputName]
    · simp [CBody.bind, resolve]

end
end Rumoca.FMI3.CountQueries
