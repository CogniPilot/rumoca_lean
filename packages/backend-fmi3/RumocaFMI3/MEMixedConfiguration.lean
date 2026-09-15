import RumocaFMI3.MERejectedInput
import RumocaFMI3.MEFailureRecovery
import RumocaFMI3.MESimulationStorage

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

/-- Logger configuration is fixed during these histories. Disabled logging
and a missing logger retain the same contracts as an enabled foreign logger. -/
inductive Configuration [CInterface] where
  | quiet (logger : Option Address) (logging : Bool)
  | logged (logger : Address) (environment : Option Address) (name : String)
      (effect : ReturningEffect (Logging.signature name))

def Configuration.Stored [CInterface] (config : Configuration) (heap : Heap) (p : Address) : Prop :=
  match config with
  | .quiet logger logging => load heap (p.member "logger") = some (.pointer logger) ∧
      load heap (p.member "logging") = some (boolean logging)
  | .logged logger environment _ _ => load heap (p.member "logger") = some (.pointer (some logger)) ∧
      load heap (p.member "logging") = some (.integer 1) ∧
      load heap (p.member "environment") = some (.pointer environment)

def Configuration.Valid [CInterface] (config : Configuration) (program : Program Invocation)
    (objects : Objects) (addresses : String → Address) (buffer : Address) : Prop :=
  match config with
  | .quiet logger logging => logger = none ∨ logging = false
  | .logged logger _ name effect => program.addresses logger = some name ∧
      program.externals name = some (External.observed (Logging.signature name) effect) ∧
      MEFailure.Respects effect objects addresses buffer

/-- Extra caller regions survive a logger whose every returning effect
preserves their object descriptions. No callback return is required. -/
def Configuration.StoragePolicy [CInterface] (config : Configuration) (region : Address → Prop) : Prop :=
  match config with
  | .quiet _ _ => True
  | .logged _ _ _ effect =>
      ∀ args before value after, effect.execute args before value after → CStorage.PreservesOn region before after

/-- Borrowed caller inputs require exact contents across every callback
return. Typed-storage preservation alone does not imply this property. -/
def Configuration.FramePolicy [CInterface] (config : Configuration) (region : Address → Prop) : Prop :=
  match config with
  | .quiet _ _ => True
  | .logged _ _ _ effect =>
      ∀ args before value after, effect.execute args before value after →
        ∀ q, region q → after q = before q

theorem Configuration.FramePolicy.storage [CInterface] {config : Configuration}
    (policy : config.FramePolicy region) : config.StoragePolicy region := by
  cases config with
  | quiet _ _ => trivial
  | logged _ _ _ _ =>
    exact fun args before value after returned => CStorage.PreservesOn.of_frame (policy args before value after returned)

theorem Configuration.FramePolicy.mono [CInterface] {config : Configuration}
    (policy : config.FramePolicy region) (subset : ∀ q, selected q → region q) :
    config.FramePolicy selected := by
  cases config with
  | quiet _ _ => trivial
  | logged _ _ _ _ =>
    exact fun args before value after returned q inside => policy args before value after returned q (subset q inside)

theorem Configuration.StoragePolicy.mono [CInterface] {config : Configuration}
    (policy : config.StoragePolicy region) (subset : ∀ q, selected q → region q) :
    config.StoragePolicy selected := by
  cases config with
  | quiet _ _ => trivial
  | logged _ _ _ _ =>
    intro args before value after returned q inside
    exact policy args before value after returned q (subset q inside)

theorem Configuration.Stored.framed [CInterface] {config : Configuration}
    (stored : config.Stored heap p)
    (frame : ∀ name ∈ ["logger", "logging", "environment"], after (p.member name) = heap (p.member name)) :
    config.Stored after p := by
  have field (name : String) (member : name ∈ ["logger", "logging", "environment"]) :
      load after (p.member name) = load heap (p.member name) := by simp only [load, frame name member]
  cases config with
  | quiet logger logging => exact ⟨(field "logger" (by simp)).trans stored.1, (field "logging" (by simp)).trans stored.2⟩
  | logged logger environment name effect => exact ⟨(field "logger" (by simp)).trans stored.1,
      (field "logging" (by simp)).trans stored.2.1, (field "environment" (by simp)).trans stored.2.2⟩

theorem configuration_outside (stored : MENumericalHistory.Stored heap p clock reference addresses buffer)
    (name : String) (member : name ∈ ["logger", "logging", "environment", "slot"]) :
    MENumericalRun.Outside p addresses buffer (p.member name) := by
  have outputs : ∀ label ∈ DiscreteCalls.names, p.member name ≠ addresses label := by
    intro label declared same
    exact stored.control.outside label declared (by simpa using (congrArg Address.block same).symm)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  refine ⟨⟨?_, Ne.symm (HistoryBodies.state_ne_field p name), stored.field_ne_buffer name⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, outputs⟩ <;> rcases member with rfl | rfl | rfl | rfl <;> simp
  · rcases member with rfl | rfl | rfl | rfl <;> simp
  · rcases member with rfl | rfl | rfl | rfl <;> simp

end Rumoca.FMI3.MEMixedRun
end
