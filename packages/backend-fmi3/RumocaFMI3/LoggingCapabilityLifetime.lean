import RumocaFMI3.LoggingCapabilityFrames
import RumocaFMI3.InstanceInitialization
import RumocaFMI3.InitializationProtocolCalls

/-! Creation supplies stored capability fields. Ordinary initialization calls
and the actual reset body preserve them. Reset retains the current logging
flag in this implementation; this theorem does not redefine the standard. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CTree CMemory CBody
variable [interface : CInterface]

theorem Capability.initialized (capability : Capability)
    (initialized : InstanceInitialization.Initialized heap p kind capability.environment capability.logger enabled) :
    capability.Configured heap p enabled :=
  ⟨⟨initialized.loggerValue, initialized.environmentValue⟩, initialized.loggingValue⟩

theorem Capability.Configured.reset {capability : Capability}
    (configured : capability.Configured heap p enabled) :
    capability.Configured (Reset.finalHeap heap p) p enabled := by
  apply configured.framed
  intro name member
  apply Reset.frame
  · exact Ne.symm (HistoryBodies.state_ne_field p name)
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp

theorem Capability.Configured.initialization_retained {capability : Capability}
    (configured : capability.Configured heap p enabled)
    (retains : InitializationProtocol.Retains p heap after) : capability.Configured after p enabled := by
  apply configured.framed
  intro name member
  apply retains
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

end Rumoca.FMI3.Logging
end
