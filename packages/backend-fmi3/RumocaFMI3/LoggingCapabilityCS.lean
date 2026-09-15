import RumocaFMI3.LoggingCapabilityFrames
import RumocaFMI3.CSRunLogging

/-! The same persistent capability supplies the existing CS logger contract.
An inactive callback keeps its host obligations for a later enable operation. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CTree CMemory CBody CCalls.Events StaticFactory
variable [interface : CInterface]

def Capability.csLogger : Capability → Option CSRun.Logger
  | .absent _ => none
  | .present logger environment name effect => some ⟨logger, environment, name, effect⟩

theorem Capability.cs_stored {capability : Capability} {logger : CSRun.Logger}
    (selected : capability.csLogger = some logger)
    (configured : capability.Configured heap p true) : logger.Stored heap p := by
  cases capability with
  | absent environment => cases selected
  | present address environment name effect =>
    cases selected
    exact ⟨configured.1.1, configured.2, configured.1.2⟩

theorem Capability.cs_bound {capability : Capability} {logger : CSRun.Logger}
    (selected : capability.csLogger = some logger) (bound : capability.Bound program) :
    logger.Bound program := by
  cases capability with
  | absent environment => cases selected
  | present address environment name effect => cases selected; exact bound

theorem Capability.cs_respects {capability : Capability} {logger : CSRun.Logger}
    (selected : capability.csLogger = some logger)
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        CSRun.ProtectedFrame objects buffers before after)) :
    logger.Respects objects buffers := by
  cases capability with
  | absent environment => cases selected
  | present address environment name effect => cases selected; exact required

theorem Capability.cs_storage {capability : Capability} {logger : CSRun.Logger}
    (selected : capability.csLogger = some logger)
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        CStorage.PreservesOn region before after)) : logger.StoragePolicy region := by
  cases capability with
  | absent environment => cases selected
  | present address environment name effect => cases selected; exact required

theorem Capability.cs_control {capability : Capability}
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after →
        CSRun.ProtectedFrame objects buffers before after))
    (inPool : p.block = objects.instances.block) : capability.ControlPolicy p := by
  apply Capability.requires_mono required
  intro name effect policy args before value after called field member
  exact policy args before value after called (p.member field) (Or.inl inPool)

end Rumoca.FMI3.Logging
end

noncomputable section

namespace Rumoca.FMI3.Logging
open CMemory CCalls.Events

theorem Capability.cs_frame [CInterface] {capability : Capability} {logger : CSRun.Logger}
    {region : Address → Prop} (selected : capability.csLogger = some logger)
    (required : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q)) :
    logger.FramePolicy region := by
  cases capability with
  | absent environment => cases selected
  | present address environment name effect => cases selected; exact required

end Rumoca.FMI3.Logging

end
