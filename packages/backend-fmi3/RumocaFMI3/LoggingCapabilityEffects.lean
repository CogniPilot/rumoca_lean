import RumocaFMI3.LoggingCapabilityCalls
import RumocaFMI3.LoggingCapabilityEnvironment

noncomputable section

namespace Rumoca.FMI3.Logging
open CMemory CBody CCalls.Events

/-- Extract the universal memory obligation from whichever callback branch
actually returned. No selected return or callback totality is assumed. -/
theorem Capability.Failure.memory [CInterface] {capability : Capability}
    {region : Address → Prop}
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        ∀ q, region q → after q = before q))
    (events : List Invocation) (result : CBody.Result)
    (failed : capability.Failure enabled heap p category messages unknown (.terminates events result)) :
    result.value = .integer 3 ∧
    CReadOnly.Preserves (LifecycleBodies.writeMode heap p .terminated) result.heap ∧
    (∀ q, region q → result.heap q = LifecycleBodies.writeMode heap p .terminated q) := by
  cases capability with
  | absent environment =>
    cases failed
    exact ⟨rfl, .refl _, fun _ _ => rfl⟩
  | present logger environment name effect =>
    cases enabled
    · cases failed
      exact ⟨rfl, .refl _, fun _ _ => rfl⟩
    · rcases failed with ⟨value, after, called, observed⟩ | ⟨_, impossible⟩
      · cases observed
        exact ⟨rfl, effect.readonly _ _ _ _ called, required _ _ _ _ called⟩
      · cases impossible

end Rumoca.FMI3.Logging

namespace Rumoca.FMI3.Logging
open CMemory CBody CCalls.Events

theorem Capability.Failure.storage [CInterface] {capability : Capability}
    {region : Address → Prop}
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        CStorage.PreservesOn region before after))
    (events : List Invocation) (result : CBody.Result)
    (failed : capability.Failure enabled heap p category messages unknown (.terminates events result)) :
    CStorage.PreservesOn region (LifecycleBodies.writeMode heap p .terminated) result.heap := by
  cases capability with
  | absent environment => cases failed; exact .refl _ _
  | present logger environment name effect =>
    cases enabled
    · cases failed; exact .refl _ _
    · rcases failed with ⟨value, after, called, observed⟩ | ⟨_, impossible⟩
      · cases observed; exact required _ _ _ _ called
      · cases impossible

theorem Capability.Failure.cases [CInterface] (capability : Capability) (enabled : Bool)
    (heap : Heap) (p category : Address) (messages : Bool → Address) (unknown : Bool) (behavior) :
    capability.Failure enabled heap p category messages unknown behavior ↔
      (∃ events status after,
        capability.Failure enabled heap p category messages unknown (.terminates events ⟨status, after⟩) ∧
        behavior = .terminates events ⟨status, after⟩) ∨
      (capability.Failure enabled heap p category messages unknown (.wrong []) ∧ behavior = .wrong []) := by
  constructor
  · intro failed
    cases capability with
    | absent environment =>
      cases failed
      exact Or.inl ⟨[], .integer 3, _, rfl, rfl⟩
    | present logger environment name effect =>
      cases enabled
      · cases failed
        exact Or.inl ⟨[], .integer 3, _, rfl, rfl⟩
      · rcases failed with ⟨value, after, called, observed⟩ | ⟨noReturn, observed⟩
        · cases observed
          exact Or.inl ⟨_, .integer 3, after, Or.inl ⟨value, after, called, rfl⟩, rfl⟩
        · cases observed
          exact Or.inr ⟨Or.inr ⟨noReturn, rfl⟩, rfl⟩
  · rintro (⟨events, status, after, failed, rfl⟩ | ⟨failed, rfl⟩) <;> exact failed

end Rumoca.FMI3.Logging

end
