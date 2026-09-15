import RumocaFMI3.LoggingCapability
import RumocaFMI3.InitializationProtocolRejection
import RumocaFMI3.MEMixedConfiguration

/-! Existing single-policy history contracts are views of the persistent
capability at a selected flag. Taking a quiet view does not discard the
capability or its universal callback obligations. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CTree CMemory CBody CCalls.Events StaticFactory
variable [interface : CInterface]

def Capability.meView (capability : Capability) (enabled : Bool) : MEMixedRun.Configuration :=
  match capability, enabled with
  | .absent _, enabled => .quiet none enabled
  | .present logger _ _ _, false => .quiet (some logger) false
  | .present logger environment name effect, true => .logged logger environment name effect

theorem Capability.me_stored {capability : Capability}
    (configured : capability.Configured heap p enabled) :
    (capability.meView enabled).Stored heap p := by
  cases capability with
  | absent environment => exact ⟨configured.1.1, configured.2⟩
  | present logger environment name effect =>
    cases enabled
    · exact ⟨configured.1.1, configured.2⟩
    · exact ⟨configured.1.1, configured.2, configured.1.2⟩

theorem Capability.me_valid {capability : Capability}
    (bound : capability.Bound program)
    (required : capability.Requires (fun _ effect => MEFailure.Respects effect objects addresses buffer))
    (enabled : Bool) :
    (capability.meView enabled).Valid program objects addresses buffer := by
  cases capability with
  | absent environment => exact Or.inl rfl
  | present logger environment name effect =>
    cases enabled
    · exact Or.inr rfl
    · exact ⟨bound.1, bound.2, required⟩

theorem Capability.me_storage {capability : Capability}
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        CStorage.PreservesOn region before after)) (enabled : Bool) :
    (capability.meView enabled).StoragePolicy region := by
  cases capability with
  | absent environment => trivial
  | present logger environment name effect =>
    cases enabled
    · trivial
    · exact required

theorem Capability.initialization_policy {capability : Capability}
    (configured : capability.Configured heap p enabled)
    (bound : capability.Bound program)
    (required : capability.Requires (fun _ effect => Float64Rejection.Respects effect objects retained))
    (writable : Reset.Writable heap (p.member "logging") .boolean) :
    InitializationProtocol.LogPolicy program objects retained heap p :=
  ⟨capability, enabled, configured, bound, required, writable⟩

end Rumoca.FMI3.Logging
end
