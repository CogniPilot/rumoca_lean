import RumocaFMI3.MEEnvironment

noncomputable section
namespace Rumoca.FMI3.MEFailure
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory

/-- Rejected numerical/control requests retain their real public arguments.
The reason selects an existing independent admission predicate and diagnostic. -/
inductive Request where
  | state (write : Bool) (reason : StateCalls.Entry.FailureReason) (buffer : Option Address) (count : UInt64)
  | derivative (access : Bool) (buffer : Option Address) (count : UInt64)
  | time (reason : TimeCalls.Failure) (bits : BitVec 64) (window : Time.Window) (minimum : Binary64.Value)
  | entry (entry : EventEntry.Entry)
  | completed (reason : CompletedCalls.Failure) (event terminate : Option Address) (flag : Bool)
  | discrete (reason : DiscreteCalls.Failure) (addresses : String → Option Address)

def Request.call (request : Request) (p : Address) : String × List Value :=
  match request with
  | .state write _ buffer count => ((StateCalls.signature write).name, StateCalls.Entry.values (some p) buffer count)
  | .derivative _ buffer count => (DerivativeCalls.signature.name, DerivativeCalls.values (some p) buffer count)
  | .time _ bits _ _ => (TimeCalls.signature.name, TimeCalls.arguments (some p) bits)
  | .entry transition => ((EventEntry.signature transition).name, [.pointer (some p)])
  | .completed _ event terminate flag => (CompletedCalls.signature.name, CompletedCalls.arguments (some p) event terminate flag)
  | .discrete _ addresses => (DiscreteCalls.signature.name, DiscreteCalls.arguments (some p) addresses)

def Request.message : Request → String
  | .state _ reason _ _ => StateCalls.Entry.failureMessage reason
  | .derivative access _ _ => DerivativeCalls.failureMessage access
  | .time reason _ _ _ => TimeCalls.failureMessage reason
  | .entry _ => ErrorCalls.rejectionMessage
  | .completed reason _ _ _ => CompletedCalls.message reason
  | .discrete reason _ => DiscreteCalls.message reason

/-- Original memory is consulted only where the actual guard reads it. A time
window failure must use bounds represented by this instance's current memory. -/
def Request.Condition (request : Request) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .state write reason buffer count => StateCalls.Entry.FailureCondition reason write kind mode heap buffer count
  | .derivative access buffer count => DerivativeCalls.FailureCondition access kind mode buffer count
  | .time reason bits window minimum => TimeCalls.FailureCondition reason kind mode window bits ∧
      (reason = .window → TimeCalls.Bounds heap p window minimum)
  | .entry transition => ¬ Reference.Allowed transition.command kind mode
  | .completed reason event terminate _ => CompletedCalls.FailureCondition reason kind mode event terminate
  | .discrete reason addresses => DiscreteCalls.FailureCondition reason kind mode addresses

def Request.Suppressed [CInterface] (request : Request) (program : CCalls.Events.Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    request.Condition heap p kind mode →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) → (logger = none ∨ logging = false) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

/-- Logging retains all returning effects and the modeled no-return case.
No successful foreign callback is a premise of this complete call contract. -/
def Request.Logged [CInterface] (request : Request) (program : CCalls.Events.Program Invocation)
    (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (kind : Kind) (mode : Mode)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    request.Condition heap p kind mode →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message request.message)

/-- Every rejection uses the same actual table and diagnostic pool as the
numerical/control calls. Earlier complete single-call contracts are retained. -/
theorem Request.prepared (request : Request) (prepared : MEEnvironment.PreparedContract model sigs pool)
    (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap) (preserved : CReadOnly.Preserves (pool.install before firstBlock signed) heap) :
    ∃ category message,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock request.message = some message ∧
      Stored signed heap category "logStatus" ∧ Stored signed heap message request.message ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : CCalls.Events.Program E),
         program.internal = LiteralPreparation.program model sigs → request.Suppressed program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : CCalls.Events.Program Invocation),
         program.internal = LiteralPreparation.program model sigs → request.Logged program category message heap signed) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  cases request with
  | state write reason buffer count =>
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messagesStored, quiet, logged⟩ :=
      prepared.states.failures header before firstBlock signed objects heap preserved
    refine ⟨category, messages reason, categoryBound, messageBound reason, categoryStored, messagesStored reason, ?_, ?_⟩
    · intro E program actual p kind mode logger logging hk hm condition hl hg suppressed
      exact quiet E program actual write reason p buffer count kind mode logger logging hk hm hl hg condition suppressed
    · intro program actual p logger environment kind mode name effect address external hk hm condition hl hg he
      exact logged program actual write reason p logger environment buffer count kind mode name effect
        address external hk hm hl hg he condition
  | derivative access buffer count =>
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messagesStored, quiet, logged⟩ :=
      prepared.derivatives.failures header before firstBlock signed objects heap preserved
    refine ⟨category, messages access, categoryBound, messageBound access, categoryStored, messagesStored access, ?_, ?_⟩
    · intro E program actual p kind mode logger logging hk hm condition hl hg suppressed
      exact quiet E program actual access p buffer count kind mode logger logging hk hm hl hg condition suppressed
    · intro program actual p logger environment kind mode name effect address external hk hm condition hl hg he
      exact logged program actual access p logger environment buffer count kind mode name effect
        address external hk hm hl hg he condition
  | time reason bits window minimum =>
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messagesStored, quiet, logged⟩ :=
      prepared.time.failures header before firstBlock signed objects heap preserved
    refine ⟨category, messages reason, categoryBound, messageBound reason, categoryStored, messagesStored reason, ?_, ?_⟩
    · intro E program actual p kind mode logger logging hk hm condition hl hg suppressed
      exact quiet E program actual p bits kind mode window minimum reason logger logging hk hm condition.2 condition.1 hl hg suppressed
    · intro program actual p logger environment kind mode name effect address external hk hm condition hl hg he
      exact logged program actual p logger environment bits kind mode window minimum reason name effect
        address external hk hm condition.2 condition.1 hl hg he
  | entry entry =>
    obtain ⟨category, message, categoryBound, messageBound, categoryStored, messageStored, quiet, logged⟩ :=
      (prepared.entry entry).failures header before firstBlock signed objects heap preserved
    refine ⟨category, message, categoryBound, messageBound, categoryStored, messageStored, ?_, ?_⟩
    · intro E program actual p kind mode logger logging hk hm condition hl hg suppressed
      exact quiet E program actual p kind mode logger logging hk hm hl hg suppressed condition
    · intro program actual p logger environment kind mode name effect address external hk hm condition hl hg he
      exact logged program actual p logger environment kind mode name effect address external hk hm hl hg he condition
  | completed reason event terminate flag =>
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messagesStored, quiet, logged⟩ :=
      prepared.completed.failures header before firstBlock signed objects heap preserved
    refine ⟨category, messages reason, categoryBound, messageBound reason, categoryStored, messagesStored reason, ?_, ?_⟩
    · intro E program actual p kind mode logger logging hk hm condition hl hg suppressed
      exact quiet E program actual p event terminate flag kind mode reason logger logging hk hm condition hl hg suppressed
    · intro program actual p logger environment kind mode name effect address external hk hm condition hl hg he
      exact logged program actual p logger environment event terminate flag kind mode reason name effect
        address external hk hm condition hl hg he
  | discrete reason addresses =>
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messagesStored, quiet, logged⟩ :=
      prepared.discrete.failures header before firstBlock signed objects heap preserved
    refine ⟨category, messages reason, categoryBound, messageBound reason, categoryStored, messagesStored reason, ?_, ?_⟩
    · intro E program actual p kind mode logger logging hk hm condition hl hg suppressed
      exact quiet E program actual p addresses kind mode reason logger logging hk hm condition hl hg suppressed
    · intro program actual p logger environment kind mode name effect address external hk hm condition hl hg he
      exact logged program actual p logger environment addresses kind mode reason name effect
        address external hk hm condition hl hg he

end Rumoca.FMI3.MEFailure
end
