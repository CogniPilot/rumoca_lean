import RumocaFMI3.LoggingCapability
import RumocaFMI3.DebugLoggingLegal

/-! A capability selects the current complete public-call contract without
losing the callback while disabled. All observed callback returns and its
blocked alternative remain explicit. Legal calls retain the same capability. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CTree CMemory CBody CCalls.Events
variable [interface : CInterface]

def Capability.Failure (capability : Capability) (enabled : Bool) (heap : Heap)
    (p category : Address) (messages : Bool → Address) (unknown : Bool)
    (behavior : Transition.Events.Observation Invocation CBody.Result) : Prop :=
  match capability, enabled with
  | .present _ environment name effect, true =>
      (∃ value after, effect.execute (arguments environment category (messages unknown))
        (LifecycleBodies.writeMode heap p .terminated) value after ∧
        behavior = .terminates [⟨name, arguments environment category (messages unknown)⟩]
          ⟨.integer 3, after⟩) ∨
      ((∀ value after, ¬ effect.execute (arguments environment category (messages unknown))
        (LifecycleBodies.writeMode heap p .terminated) value after) ∧ behavior = .wrong [])
  | _, _ => behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩

theorem Capability.request_contract (capability : Capability) (enabled : Bool)
    (program : Program Invocation) (heap : Heap) (p category : Address) (messages : Bool → Address)
    (kind : Kind) (mode : Mode)
    (configured : capability.Configured heap p enabled) (bound : capability.Bound program)
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (quiet : DebugLogging.SuppressedContract program heap)
    (logged : DebugLogging.LoggedContract program heap category messages) :
    DebugLogging.RequestContract program heap p kind mode (capability.Failure enabled heap p category messages) := by
  cases capability with
  | absent environment =>
    exact quiet p kind mode none enabled hm configured.1.1 configured.2 (Or.inl rfl)
  | present logger environment name effect =>
    cases enabled
    · exact quiet p kind mode (some logger) false hm configured.1.1 configured.2 (Or.inr rfl)
    · have called := logged p logger environment kind mode name (External.observed (signature name) effect)
        bound.1 bound.2 rfl hm configured.1.1 configured.2 configured.1.2
      have same : (fun unknown behavior =>
          (∃ events value final,
            (External.observed (signature name) effect).execute
              (arguments environment category (messages unknown))
              (LifecycleBodies.writeMode heap p .terminated) events value final ∧
            behavior = .terminates events ⟨.integer 3, final⟩) ∨
          ((∀ events value final,
            ¬ (External.observed (signature name) effect).execute
              (arguments environment category (messages unknown))
              (LifecycleBodies.writeMode heap p .terminated) events value final) ∧ behavior = .wrong [])) =
          (Capability.present logger environment name effect).Failure true heap p category messages := by
        funext unknown behavior
        exact propext (observed_choices effect (arguments environment category (messages unknown))
          (LifecycleBodies.writeMode heap p .terminated) (fun _ final => ⟨.integer 3, final⟩) behavior)
      rw [same] at called
      exact called

theorem Capability.legal_returned (capability : Capability) (program : Program Invocation)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (failures)
    (contract : DebugLogging.RequestContract program heap p kind mode failures)
    (stored : capability.Stored heap p) (bound : capability.Bound program)
    (required : capability.Requires policy)
    (pointer : Option Address) (count : UInt64) (enabled : Bool) (old : Option Value)
    (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (caller : pointer.isSome = true → DebugLogging.Entries heap pointer count.toNat selected bytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩)
    (legal : DebugLogging.LegalRequest pointer count.toNat selected bytes ["logStatus"])
    (events : List Invocation) (result : CBody.Result)
    (executed : (machine program).Behaves
      (.calling DebugLogging.signature.name (DebugLogging.arguments (some p) enabled count pointer) heap .done)
      (.terminates events result)) :
    events = [] ∧ result.value = .integer 0 ∧ capability.Configured result.heap p enabled ∧
    capability.Bound program ∧ capability.Requires policy ∧
    CStorage.Preserves heap result.heap ∧ CReadOnly.Preserves heap result.heap := by
  obtain ⟨eventsEqual, status, flag, storageFrame, readonly, frame⟩ :=
    DebugLogging.legal_returned program heap p kind mode failures contract pointer count enabled old
      selected bytes hk hm caller storage legal events result executed
  refine ⟨eventsEqual, status, ⟨?_, flag⟩, bound, required, storageFrame, readonly⟩
  apply stored.framed
  intro name member
  apply frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp

end Rumoca.FMI3.Logging
end
