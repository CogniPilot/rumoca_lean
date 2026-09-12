import RumocaC.CallEvents

/-! Explicitly observable importer calls. This is a reusable adapter from a
host effect relation to external-call semantics; it records the actual symbol
and converted arguments, and does not silently assume the host returns. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory
variable [interface : CInterface]

structure Invocation where
  name : String
  arguments : List Value
  deriving DecidableEq

/-- A relation on returning host outcomes. Termination/uniqueness, when needed,
are separate invocation-local premises. Writable effects remain unrestricted. -/
structure ReturningEffect (signature : Signature) where
  execute : List Value → Heap → Value → Heap → Prop
  result_typed : ∀ args before result after, execute args before result after →
    returnCast signature.result result = some result
  readonly : ∀ args before result after, execute args before result after →
    CReadOnly.Preserves before after

def External.observed (signature : Signature) (effect : ReturningEffect signature) : External Invocation where
  signature := signature
  execute args before events result after :=
    events = [⟨signature.name, args⟩] ∧ effect.execute args before result after
  result_typed _ _ _ _ _ performed := effect.result_typed _ _ _ _ performed.2
  readonly _ _ _ _ _ performed := effect.readonly _ _ _ _ performed.2

theorem observed_outcome (effect : ReturningEffect signature) :
    (External.observed signature effect).execute args before events result after ↔
      events = [⟨signature.name, args⟩] ∧ effect.execute args before result after := Iff.rfl

theorem observed_unique (effect : ReturningEffect signature)
    (unique : ∀ value out, effect.execute args before value out → value = result ∧ out = after) :
    ∀ events value out, (External.observed signature effect).execute args before events value out →
      events = [⟨signature.name, args⟩] ∧ value = result ∧ out = after := by
  intro events value out performed
  exact ⟨performed.1, unique value out performed.2⟩

theorem observed_choices (effect : ReturningEffect sig) (args : List Value) (heap : Heap)
    (resultOf : Value → Heap → CBody.Result) (behavior : Transition.Events.Observation Invocation CBody.Result) :
    ((∃ events value after, (External.observed sig effect).execute args heap events value after ∧
      behavior = .terminates events (resultOf value after)) ∨
      ((∀ events value after, ¬ (External.observed sig effect).execute args heap events value after) ∧
        behavior = .wrong [])) ↔
    ((∃ value after, effect.execute args heap value after ∧
      behavior = .terminates [⟨sig.name, args⟩] (resultOf value after)) ∨
      ((∀ value after, ¬ effect.execute args heap value after) ∧ behavior = .wrong [])) := by
  have absent : (∀ events value after, ¬ (External.observed sig effect).execute args heap events value after) ↔
      (∀ value after, ¬ effect.execute args heap value after) := by
    constructor
    · intro missing value after executed
      exact missing [⟨sig.name, args⟩] value after ⟨rfl, executed⟩
    · intro missing events value after executed
      exact missing value after executed.2
  rw [absent]
  simp [External.observed]

end Rumoca.CCalls.Events
