import RumocaFMI3.InitializationAccessStorage
import RumocaFMI3.ResetStorage
import RumocaFMI3.CSRunLogging

noncomputable section
namespace Rumoca.FMI3
open CMemory Float64Access
namespace InitializationAccess

def runReference (state : ModelExchange.State) (args : Initialization.Arguments)
    (before during : List Request) : CSRun.Reference :=
  ⟨(finalState during (finalState before state)).x, args.start, ⟨args.start, 0⟩, args.stopTime, .step⟩

variable [CInterface] {program : CCalls.Events.Program E}

theorem Certificate.retains
    (certified : Certificate model program p buffers args kind state time heap before during beforeEntry atExit) :
    CSRun.Retains p heap (InitializationBodies.exitHeap atExit p kind) :=
  fun name retained => certified.field name retained

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
