import RumocaFMI3.InitializationAccessStorage
import RumocaFMI3.CSRunLogging

noncomputable section
namespace Rumoca.FMI3
open CMemory Float64Access

theorem Reset.Storage.preserved (stored : Reset.Storage heap p) (preserved : CStorage.Preserves heap after) :
    Reset.Storage after p := by
  have keep {address type} (cell : Reset.Writable heap address type) : Reset.Writable after address type := by
    obtain ⟨old, found⟩ := cell
    exact preserved.cell found
  exact ⟨keep stored.state, keep stored.time, keep stored.minimum, keep stored.event,
    keep stored.completed, keep stored.stop, keep stored.stopDefined, keep stored.mode⟩

namespace InitializationAccess

def runReference (state : ModelExchange.State) (args : Initialization.Arguments)
    (before during : List Request) : CSRun.Reference :=
  ⟨(finalState during (finalState before state)).x, args.start, ⟨args.start, 0⟩, args.stopTime, .step⟩

variable [CInterface] {program : CCalls.Events.Program E}

theorem Certificate.retains
    (certified : Certificate model program p buffers args kind state time heap before during beforeEntry atExit) :
    CSRun.Retains p heap (InitializationBodies.exitHeap atExit p kind) := by
  intro name retained
  have different (field : String) (member : field ∈ writtenFields) : p.member name ≠ p.member field := by
    intro same
    have names := (Address.member_inj _ _ _).mp same
    exact retained (names ▸ member)
  exact (InitializationBodies.exit_frame atExit p (p.member name) kind (different "mode" (by simp [writtenFields]))).trans
    ((certified.atExitFields name).trans
      ((InitializationEntry.frame beforeEntry p (p.member name) args
        (different "time" (by simp [writtenFields])) (different "timeMin" (by simp [writtenFields]))
        (different "eventTime" (by simp [writtenFields])) (different "lastCompleted" (by simp [writtenFields]))
        (different "stop" (by simp [writtenFields])) (different "stopDefined" (by simp [writtenFields]))
        (different "mode" (by simp [writtenFields]))).trans (certified.beforeFields name)))

theorem Certificate.cs_run_storage
    (certified : Certificate model program p buffers args .cs state time heap before during beforeEntry atExit)
    (admissible : args.Admissible) (outputs : StepArguments.Storage heap p stepBuffers)
    (reset : Reset.Storage heap p) :
    CSRun.Stored model.solve (InitializationBodies.exitHeap atExit p .cs) p stepBuffers
      (runReference state args before during) := by
  have stored := certified.cs_storage admissible outputs
  exact ⟨stored.kind, stored.mode, stored.clock, stored.state, stored.stopDefined, stored.stopValue,
    reset.preserved certified.storage, stored.buffers⟩

end InitializationAccess
end Rumoca.FMI3
end
