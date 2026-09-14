import RumocaFMI3.InitializationAccessStorage
import RumocaFMI3.MENumericalInitialization
import RumocaFMI3.MEMixedLifecycle
import RumocaFMI3.ResetStorage

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CMemory Float64Access

def meReference (state : ModelExchange.State) (args : Initialization.Arguments)
    (before during : List Request) : MENumericalHistory.ReferenceState :=
  MENumericalHistory.ReferenceState.initial args (finalState during (finalState before state)).x

variable [CInterface] {program : CCalls.Events.Program E}

/-- The actual post-access exit heap supplies ME Event Mode, the selected
state, initial event-iteration duty, clock/stop policy and reusable caller
storage. No initialized heap or future getter buffer is assumed. -/
theorem Certificate.me_storage
    (certified : Certificate model program p access args .me state time heap before during beforeEntry atExit)
    (admissible : args.Admissible)
    (outputs : MENumericalHistory.CallerStorage heap p addresses buffer) :
    MENumericalHistory.Stored (InitializationBodies.exitHeap atExit p .me) p (Time.Clock.initial args.start)
      (meReference state args before during) addresses buffer := by
  have callers := outputs.storage_preserved certified.storage
  have fields (name : String) (notMode : name ≠ "mode") :
      load (InitializationBodies.exitHeap atExit p .me) (p.member name) =
        load (InitializationEntry.finalHeap beforeEntry p args) (p.member name) := by
    simp only [load, InitializationBodies.exit_frame atExit p (p.member name) .me
      (by simpa using notMode), certified.atExitFields]
  refine ⟨⟨certified.instanceStored.kind, certified.instanceStored.mode, certified.clockStored,
    Time.initial_represents args.start args.stopTime, certified.instanceStored.represented, ?_, ?_,
    callers.controls, callers.outside⟩, certified.instanceStored.state, callers.bufferCell,
    callers.bufferOutside, callers.bufferSeparate⟩
  · rw [fields "stopDefined" (by decide)]
    change load (InitializationEntry.finalHeap beforeEntry p args) (p.member "stopDefined") =
      some (CBody.boolean args.stopTime.isSome)
    simpa only [Initialization.stopTime_defined args admissible] using (InitializationEntry.stop beforeEntry p args).2
  · intro limit selected
    rw [fields "stop" (by decide)]
    simpa only [Value.finite, Initialization.stopTime_bits args admissible limit selected]
      using (InitializationEntry.stop beforeEntry p args).1

theorem Certificate.configuration {config : MEMixedRun.Configuration}
    (certified : Certificate model program p access args kind state time heap before during beforeEntry atExit)
    (configured : config.Stored heap p) :
    config.Stored (InitializationBodies.exitHeap atExit p kind) p := by
  apply configured.framed
  intro name member
  apply certified.field
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

end Rumoca.FMI3.InitializationAccess
end
