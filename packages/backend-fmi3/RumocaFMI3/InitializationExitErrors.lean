import RumocaFMI3.InitializationExit
import RumocaFMI3.LoggingContract
import RumocaC.ObservedCalls

noncomputable section
namespace Rumoca.FMI3.InitializationExit
open CTree CMemory CLiteral CCalls.Events

def FailureExecutionContract [interface : CInterface]
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (kind : Kind) (mode : Mode)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    mode ≠ .initialization →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p)) heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message ErrorCalls.rejectionMessage)

def SilentExecutionContract [interface : CInterface]
    (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (kind : Kind) (mode : Mode) (logger : Option Address),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (.integer 0) →
    mode ≠ .initialization →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem failure_execution_correct (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program Invocation) (category message : Address) (heap : Heap) (signed : Bool)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (literal : static.addresses "logStatus" = some category)
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (categoryStored : Stored signed heap category "logStatus")
    (messageStored : Stored signed heap message ErrorCalls.rejectionMessage) :
    FailureExecutionContract program category message heap signed := by
  intro p logger environment kind mode name effect address external hk hm hl hg he denied
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_prefix model heap p kind mode hk modeLoaded denied
  have all := GuardedCalls.FailurePrefix.all_behaviors program (Runtime.function model signature) (arguments (some p))
    heap heap p message category logger ErrorCalls.rejectionMessage name environment _
    (External.observed (Logging.signature name) effect) certified defined helper messageBound
    address external rfl literal hm hl hg he
  constructor
  · intro behavior
    exact (all behavior).trans (observed_choices effect _ _ (fun _ after => ⟨.integer 3, after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, Logging.arguments environment category message⟩]
      ⟨.integer 3, after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := CCalls.Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, messageStored.preserved preserved⟩

theorem silent_execution_correct (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (message : Address) (heap : Heap)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message) :
    SilentExecutionContract program heap := by
  intro p kind mode logger hk hm hl hg denied behavior
  have modeLoaded : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hm, convert, Mode.code]
  have certified := failure_prefix model heap p kind mode hk modeLoaded denied
  exact GuardedCalls.FailurePrefix.silent_behaviors program (Runtime.function model signature) (arguments (some p))
    heap heap p message ErrorCalls.rejectionMessage _ logger certified defined helper messageBound hm hl hg behavior

end
end Rumoca.FMI3.InitializationExit
