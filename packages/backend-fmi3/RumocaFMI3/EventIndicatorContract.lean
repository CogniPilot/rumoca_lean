import RumocaFMI3.EventIndicatorCalls
import RumocaC.ObservedCalls

noncomputable section
namespace Rumoca.FMI3.EventIndicatorCalls
open CTree CMemory CLiteral CCalls.Events

def FailureExecutionContract [interface : CInterface] (access : Bool)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment buffer : Option Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    FailureCondition access kind mode count →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (values (some p) buffer count) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message (failureMessage access))

structure QuietContract [CInterface] (program : CCalls.Events.Program E) (heap : Heap) : Prop where
  get : ∀ (p : Address) (buffer : Option Address) (mode : Mode),
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getDerivatives .me mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (values (some p) buffer 0) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩
  null : ∀ buffer count behavior, (CCalls.Events.machine program).Behaves
    (.calling signature.name (values none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem failure_message_collected (model : Solve.FMI3Model source) (access : Bool) :
    failureMessage access ∈ functionTexts (Runtime.function model signature) := by
  cases access <;> simp [failureMessage, ErrorCalls.rejectionMessage, Runtime.function, body_eq, tail,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail,
    Runtime.ret, Runtime.negate, Runtime.call, Runtime.v, Runtime.n, Runtime.nev, Runtime.ok,
    functionTexts, statementTexts, expressionTexts]

end Rumoca.FMI3.EventIndicatorCalls
end
