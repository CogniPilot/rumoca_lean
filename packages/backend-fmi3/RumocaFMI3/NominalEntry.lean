import RumocaFMI3.NominalFailures
import RumocaFMI3.GuardedCalls
import RumocaC.ObservedCalls

noncomputable section
namespace Rumoca.FMI3.Nominals
open CTree CMemory CBody CLiteral CCalls.Events

theorem body_eq (model : Solve.FMI3Model source) :
    Runtime.body model ErrorCalls.nominalSignature =
      Runtime.require .getNominals ++ ErrorCalls.nominalRest := by
  simp [Runtime.body, ErrorCalls.nominalSignature, ErrorCalls.nominalRest]

section
variable [static : StaticLiterals]
private local instance entryInterface : CInterface := cInterface static.addresses

/-- The lifecycle guard precedes the output-size/pointer guard. This stops
before the shared failure helper and transports to the actual runtime. -/
theorem failure_prefix (model : Solve.FMI3Model source) (access : Bool)
    (heap : Heap) (p : Address) (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (condition : FailureCondition access kind mode buffer count) :
    GuardedCalls.FailurePrefix (Runtime.function model ErrorCalls.nominalSignature)
      (ErrorCalls.nominalArguments p buffer count) heap p (failureMessage access) heap := by
  cases access with
  | false =>
    refine ⟨rfl, BodyEmbedding.body_closed model ErrorCalls.nominalSignature,
      ErrorCalls.nominalEnv p buffer count,
      CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p)),
      ErrorCalls.nominalRest, 3, ErrorCalls.nominal_parameters p buffer count, ?_, ?_, ?_⟩
    · have executed := LifecycleGuard.reject_prefix (ErrorCalls.nominalEnv p buffer count) heap p
        .getNominals kind mode ErrorCalls.nominalRest
        (by simp [ErrorCalls.nominalEnv, CBody.bind])
        (by simp [ErrorCalls.nominalEnv, CBody.bind]) hk hm condition
      rw [← body_eq model] at executed
      exact executed
    · simp [ErrorCalls.nominalEnv, CBody.bind]
    · simp [CBody.bind, CBody.resolve]
  | true =>
    obtain ⟨allowed, invalid⟩ := condition
    refine ⟨rfl, BodyEmbedding.body_closed model ErrorCalls.nominalSignature,
      ErrorCalls.nominalEnv p buffer count,
      CBody.bind (ErrorCalls.nominalEnv p buffer count) "m" (.pointer (some p)),
      accessRest, 4, ErrorCalls.nominal_parameters p buffer count,
      invalid_body model heap p buffer count kind mode hk hm allowed invalid, ?_, ?_⟩
    · simp [ErrorCalls.nominalEnv, CBody.bind]
    · simp [CBody.bind, CBody.resolve]

end

def FailureExecutionContract [interface : CInterface]
    (access : Bool) (program : CCalls.Events.Program Invocation) (category message : Address)
    (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment buffer : Option Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    FailureCondition access kind mode buffer count →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p buffer count) heap .done)
      behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message (failureMessage access))


structure QuietExecutionContract [interface : CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop where
  successful : ∀ p buffer kind mode old,
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getNominals kind mode →
    heap buffer = some ⟨.float64, true, old⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling ErrorCalls.nominalSignature.name (ErrorCalls.nominalArguments p (some buffer) 1) heap .done)
      behavior ↔ behavior = .terminates [] ⟨.integer 0, written heap buffer⟩
  null : ∀ buffer (count : UInt64) behavior, (CCalls.Events.machine program).Behaves
    (.calling ErrorCalls.nominalSignature.name [.pointer none, .pointer buffer, .integer count.toNat] heap .done)
    behavior ↔ behavior = .terminates [] ⟨.integer 3, heap⟩


end Rumoca.FMI3.Nominals
end
