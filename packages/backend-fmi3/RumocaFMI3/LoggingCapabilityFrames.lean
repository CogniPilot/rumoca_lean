import RumocaFMI3.LoggingCapabilityCalls
import RumocaFMI3.Float64RejectionMemory
import RumocaFMI3.MEFailureMemory

/-! Existing universal host-memory contracts imply preservation of persistent
logging information. A rejected setter retains the old flag, including across
every returning callback branch; no return is required by these policies. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CTree CMemory CBody CCalls.Events StaticFactory
variable [interface : CInterface]

def Capability.ControlPolicy (capability : Capability) (p : Address) : Prop :=
  capability.Requires (fun _ effect =>
    ∀ args before value after, effect.execute args before value after →
      ∀ name ∈ ["logger", "environment", "logging"], after (p.member name) = before (p.member name))

theorem Capability.initialization_control {capability : Capability}
    (required : capability.Requires (fun _ effect => Float64Rejection.Respects effect objects retained))
    (inPool : p.block = objects.instances.block) : capability.ControlPolicy p := by
  apply Capability.requires_mono required
  intro name effect policy args before value after called field member
  exact (policy args before value after called).record inPool _ (p.member_in_record field)

theorem Capability.me_control {capability : Capability}
    (required : capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer))
    (inPool : p.block = objects.instances.block) : capability.ControlPolicy p := by
  apply Capability.requires_mono required
  intro name effect policy args before value after called field member
  exact policy args before value after called (p.member field) (Or.inl inPool)

theorem Capability.Configured.mode_written {capability : Capability}
    (configured : capability.Configured heap p enabled) (mode : Mode) :
    capability.Configured (LifecycleBodies.writeMode heap p mode) p enabled := by
  refine ⟨configured.1.mode_written mode, ?_⟩
  simpa only [load, LifecycleBodies.write_frame heap p (p.member "logging") mode (by simp)] using configured.2

theorem Capability.Failure.returned {capability : Capability}
    (configured : capability.Configured heap p enabled) (policy : capability.ControlPolicy p)
    (events : List Invocation) (result : CBody.Result)
    (failed : capability.Failure enabled heap p category messages unknown (.terminates events result)) :
    result.value = .integer 3 ∧ capability.Configured result.heap p enabled := by
  cases capability with
  | absent environment =>
    cases failed
    exact ⟨rfl, configured.mode_written .terminated⟩
  | present logger environment name effect =>
    cases enabled
    · cases failed
      exact ⟨rfl, configured.mode_written .terminated⟩
    · rcases failed with ⟨value, after, called, observed⟩ | ⟨_, impossible⟩
      · cases observed
        exact ⟨rfl, (configured.mode_written .terminated).framed (policy _ _ _ _ called)⟩
      · cases impossible

theorem Capability.Failure.progress (capability : Capability) (enabled : Bool)
    (heap : Heap) (p category : Address) (messages : Bool → Address) (unknown : Bool) :
    (∃ events status after,
      capability.Failure enabled heap p category messages unknown (.terminates events ⟨status, after⟩)) ∨
    capability.Failure enabled heap p category messages unknown (.wrong []) := by
  cases capability with
  | absent environment => exact Or.inl ⟨[], .integer 3, _, rfl⟩
  | present logger environment name effect =>
    cases enabled
    · exact Or.inl ⟨[], .integer 3, _, rfl⟩
    · classical
      by_cases returns : ∃ value after, effect.execute (arguments environment category (messages unknown))
          (LifecycleBodies.writeMode heap p .terminated) value after
      · obtain ⟨value, after, called⟩ := returns
        exact Or.inl ⟨[⟨name, arguments environment category (messages unknown)⟩], .integer 3,
          after, Or.inl ⟨value, after, called, rfl⟩⟩
      · exact Or.inr (Or.inr ⟨fun value after called => returns ⟨value, after, called⟩, rfl⟩)

end Rumoca.FMI3.Logging
end
