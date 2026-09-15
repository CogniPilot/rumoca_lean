import RumocaFMI3.InitializationProtocolRunFrames
import RumocaFMI3.CSRunLoggedExecution
import RumocaFMI3.CSRunProgress
import RumocaFMI3.CSRunEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory StaticFactory CCalls.Events
variable {readers : ReadBank}

/-- Resources shared by initialization and simulation. The original caller
bank and literal heap stay fixed across every reset and handoff. -/
structure Persistent [CInterface] (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (original literals heap : Heap) (p : Address) (readers : ReadBank) : Prop where
  ownership : SlotOwners.Represents objects.flagsBlock heap owners
  caller : CallerStorage objects retained original heap
  readonly : CReadOnly.Preserves literals heap
  logging : LogPolicy program objects retained heap p
  readerFrame : readers.Frame original heap

theorem Invariant.persistent [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity}
    (invariant : Invariant program objects retained owners original literals heap p kind state readers) :
    Persistent program objects retained owners original literals heap p readers :=
  ⟨invariant.ownership, invariant.caller, invariant.readonly, invariant.logging, invariant.readerFrame⟩

/-- The initialization logger policy supplies the simulation policy at the
actual handoff heap. No configuration from the first factory heap is needed. -/
theorem LogPolicy.cs [CInterface] {program : Program Invocation}
    (logging : LogPolicy program objects retained heap p)
    (guarded : CSOutputsGuarded objects retained buffers) :
    CSRun.Suppressed heap p ∨ ∃ logger : CSRun.Logger,
      logger.Stored heap p ∧ logger.Bound program ∧ logger.Respects objects buffers ∧
      logger.StoragePolicy (Float64Rejection.Protected objects retained) ∧
      logger.FramePolicy (Float64Rejection.Protected objects retained) := by
  rcases logging.current with quiet |
    ⟨pointer, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · exact Or.inl quiet
  · refine Or.inr ⟨⟨pointer, environment, name, effect⟩,
      ⟨loggerValue, loggingValue, environmentValue⟩, ⟨address, external⟩, ?_, ?_, respects⟩
    · intro args before value after returned q inside
      exact respects args before value after returned q (guarded.protects inside)
    · intro args before value after returned
      exact CStorage.PreservesOn.of_frame (respects args before value after returned)

theorem LogPolicy.me [CInterface] {program : Program Invocation}
    (logging : LogPolicy program objects retained heap p)
    (guarded : MEOutputsGuarded objects retained addresses buffer) :
    ∃ config : MEMixedRun.Configuration, config.Stored heap p ∧ config.Valid program objects addresses buffer ∧
      config.StoragePolicy (Float64Rejection.Protected objects retained) ∧
      config.FramePolicy (Float64Rejection.Protected objects retained) := by
  rcases logging.current with ⟨logger, enabled, loggerValue, loggingValue, quiet⟩ |
    ⟨pointer, environment, name, effect, loggerValue, loggingValue, environmentValue, address, external, respects⟩
  · exact ⟨.quiet logger enabled, ⟨loggerValue, loggingValue⟩, quiet, trivial, trivial⟩
  · refine ⟨.logged pointer environment name effect,
      ⟨loggerValue, loggingValue, environmentValue⟩, ⟨address, external, ?_⟩, ?_, respects⟩
    · intro args before value after returned q inside
      exact respects args before value after returned q (guarded.protects inside)
    · intro args before value after returned
      exact CStorage.PreservesOn.of_frame (respects args before value after returned)

end Rumoca.FMI3.InitializationProtocol
end
