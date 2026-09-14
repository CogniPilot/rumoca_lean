import RumocaFMI3.Float64Environment
import RumocaFMI3.Float64SetEnvironment

noncomputable section
namespace Rumoca.FMI3.Float64Rejection
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory

/-- Rejected accessor calls retain their actual public arguments and raw
input snapshot. Reasons instantiate the existing independent guard predicates. -/
inductive Request where
  | get (reason : Float64Calls.GetFailure) (input buffer : Option Address)
      (n m : UInt64) (references : Nat → UInt32)
  | set (reason : Float64Set.Failure) (input buffer : Option Address)
      (n m : UInt64) (references : Nat → UInt32) (bits : Nat → BitVec 64)

def Request.call (request : Request) (p : Address) : String × List Value :=
  match request with
  | .get _ input buffer n m _ => ((Float64Calls.signature false).name,
      Float64Calls.arguments (some p) input buffer n m)
  | .set _ input buffer n m _ _ => ((Float64Calls.signature true).name,
      Float64Calls.arguments (some p) input buffer n m)

def Request.message : Request → String
  | .get reason _ _ _ _ _ => Float64Calls.failureMessage reason
  | .set reason _ _ _ _ _ _ => Float64Set.failureMessage reason

def Request.Condition (request : Request) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .get reason input buffer n m references => Reference.Allowed .get kind mode ∧
      Float64Calls.FailureCondition reason input buffer n m references
  | .set reason input buffer n m references bits =>
      Float64Set.FailureCondition reason kind mode input buffer n m references bits

/-- Early lifecycle/array guards require no input snapshot. Entry validation
requires values only at references selecting the state, preserving short circuiting. -/
def Request.Readable (request : Request) (heap : Heap) : Prop :=
  match request with
  | .get reason input _ n _ references =>
      reason = .reference → Float64Calls.References heap input n.toNat references
  | .set reason input buffer n _ references bits =>
      reason = .entry → Float64Calls.References heap input n.toNat references ∧
        Float64Set.ReadableValues heap buffer n.toNat references bits

def Request.Suppressed [CInterface] (request : Request) (program : Program E) (heap : Heap) : Prop :=
  ∀ (p : Address) (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    request.Condition kind mode → request.Readable heap →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) → (logger = none ∨ logging = false) →
    ∀ behavior, (machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

def Request.Logged [CInterface] (request : Request) (program : Program Invocation)
    (category message : Address) (heap : Heap) (signed : Bool) : Prop :=
  ∀ (p logger : Address) (environment : Option Address) (kind : Kind) (mode : Mode)
    (name : String) (effect : ReturningEffect (Logging.signature name)),
    program.addresses logger = some name →
    program.externals name = some (External.observed (Logging.signature name) effect) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    request.Condition kind mode → request.Readable heap →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    (∀ behavior, (machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done) behavior ↔
      (∃ value after, effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (Logging.arguments environment category message)
      (LifecycleBodies.writeMode heap p .terminated) value after →
      Stored signed after category "logStatus" ∧ Stored signed after message request.message)

theorem Request.prepared (request : Request)
    (getter : Float64Environment.PreparedContract model sigs pool)
    (setter : Float64SetEnvironment.PreparedContract model sigs pool)
    (header : CFenv.Header) (before : Heap) (firstBlock : Nat) (signed : Bool)
    (objects : Objects) (heap : Heap) (preserved : CReadOnly.Preserves (pool.install before firstBlock signed) heap) :
    ∃ category message,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock request.message = some message ∧
      Stored signed heap category "logStatus" ∧ Stored signed heap message request.message ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (E : Type) (program : Program E),
         program.internal = LiteralPreparation.program model sigs → request.Suppressed program heap) ∧
      (letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
       ∀ (program : Program Invocation),
         program.internal = LiteralPreparation.program model sigs → request.Logged program category message heap signed) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  cases request with
  | get reason input buffer n m references =>
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messagesStored, quiet, logged⟩ :=
      getter.failures header before firstBlock signed objects heap preserved
    refine ⟨category, messages reason, categoryBound, messageBound reason, categoryStored, messagesStored reason, ?_, ?_⟩
    · intro E program actual p kind mode logger logging hk hm condition readable hl hg suppressed
      exact quiet E program actual reason p input buffer n m references kind mode logger logging
        hk hm hl hg condition.1 readable condition.2 suppressed
    · intro program actual p logger environment kind mode name effect address external hk hm condition readable hl hg he
      exact logged program actual reason p logger environment input buffer n m references kind mode name effect
        address external hk hm hl hg he condition.1 readable condition.2
  | set reason input buffer n m references bits =>
    obtain ⟨category, messages, categoryBound, messageBound, categoryStored, messagesStored, quiet, logged⟩ :=
      setter.failures header before firstBlock signed objects heap preserved
    refine ⟨category, messages reason, categoryBound, messageBound reason, categoryStored, messagesStored reason, ?_, ?_⟩
    · intro E program actual p kind mode logger logging hk hm condition readable hl hg suppressed
      exact quiet E program actual reason p input buffer n m references bits kind mode logger logging
        hk hm hl hg readable condition suppressed
    · intro program actual p logger environment kind mode name effect address external hk hm condition readable hl hg he
      exact logged program actual reason p logger environment input buffer n m references bits kind mode name effect
        address external hk hm hl hg he readable condition

end Rumoca.FMI3.Float64Rejection
end
