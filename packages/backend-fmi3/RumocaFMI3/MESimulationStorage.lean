import RumocaFMI3.MENumericalRun
import RumocaFMI3.RestartStorage
import RumocaFMI3.MERejectedInput
import RumocaC.StorageWrites

noncomputable section
namespace Rumoca.FMI3.HistoryProofs
open CMemory

theorem write_storage (found : heap (p.member name) = some (cell old)) (value : Binary64.Value) :
    CStorage.Preserves heap (write heap p name value) :=
  CStorage.replace_typed found _ rfl rfl

theorem raise_storage (found : heap (p.member name) = some (cell old)) (current value : Binary64.Value) :
    CStorage.Preserves heap (raiseHeap heap p name current value) := by
  unfold raiseHeap
  split
  · exact write_storage found value
  · exact .refl heap

theorem event_storage (stored : Stored heap p clock) : CStorage.Preserves heap (eventHeap heap p clock) :=
  (write_storage stored.eventTime clock.time).trans
    (raise_storage (write_event stored clock.time).minimum clock.minimum clock.time)

theorem completed_storage (stored : Stored heap p clock) : CStorage.Preserves heap (completedHeap heap p clock) :=
  (write_storage stored.minimum clock.eventTime).trans
    ((raise_storage (write_minimum stored clock.eventTime).minimum clock.eventTime clock.lastCompleted).trans
      (write_storage (raise_minimum (write_minimum stored clock.eventTime) clock.lastCompleted).lastCompleted clock.time))

end Rumoca.FMI3.HistoryProofs

namespace Rumoca.FMI3.MEHistory
open CTree CMemory

theorem action_storage (stored : Stored heap p clock reference model addresses) (action : Action) :
    CStorage.Preserves heap (action.heap heap p clock addresses) := by
  cases action with
  | setTime time => exact HistoryProofs.write_storage stored.clockStored.time time
  | enter entry =>
    cases entry with
    | continuous => exact CStorage.replace_typed stored.mode _ rfl rfl
    | event =>
      have modeAfter : HistoryProofs.eventHeap heap p clock (p.member "mode") =
          some ⟨.int32, true, some (.integer reference.mode.code)⟩ := by
        rw [HistoryProofs.event_frame heap p (p.member "mode") clock (by simp) (by simp)]
        exact stored.mode
      exact (HistoryProofs.event_storage stored.clockStored).trans (CStorage.replace_typed modeAfter _ rfl rfl)
  | updateDiscrete => exact COutputAssignments.after_storage stored.buffers.writable
  | completed _ =>
    have event : HistoryBodies.BoolWritable heap (addresses "discreteStatesNeedUpdate") :=
      stored.buffers ("discreteStatesNeedUpdate", .boolean) (by decide +kernel)
    have terminate : HistoryBodies.BoolWritable
        (HistoryBodies.zero heap (addresses "discreteStatesNeedUpdate")) (addresses "terminateSimulation") :=
      HistoryBodies.zero_writable (stored.buffers ("terminateSimulation", .boolean) (by decide +kernel)) _
    obtain ⟨oldEvent, event⟩ := event
    obtain ⟨oldTerminate, terminate⟩ := terminate
    exact (CStorage.replace_typed event ⟨.boolean, true, some (.integer 0)⟩ rfl rfl).trans
      ((CStorage.replace_typed terminate ⟨.boolean, true, some (.integer 0)⟩ rfl rfl).trans
        (HistoryProofs.completed_storage (HistoryBodies.outputs_stored stored.clockStored _ _
          (stored.outside "discreteStatesNeedUpdate" (by decide +kernel))
          (stored.outside "terminateSimulation" (by decide +kernel)))))

end Rumoca.FMI3.MEHistory

namespace Rumoca.FMI3.MENumericalHistory
open CTree CMemory

theorem action_storage (model : Solve.FMI3Model source)
    (stored : Stored heap p clock reference addresses buffer) (action : Action) :
    CStorage.Preserves heap (action.after model heap p clock reference addresses buffer) := by
  cases action with
  | control command => exact MEHistory.action_storage stored.control command
  | setState value =>
    obtain ⟨old, cell⟩ := stored.bufferCell
    exact (CStorage.replace_typed cell ⟨.float64, true, some (.finite value)⟩ rfl rfl).trans
      (CStorage.replace_typed (stored.write_buffer value).stateCell ⟨.float64, true, some (.finite value)⟩ rfl rfl)
  | getState | derivative =>
    obtain ⟨old, cell⟩ := stored.bufferCell
    exact CStorage.replace_typed cell _ rfl rfl

theorem restart_storage (model : Solve.FMI3Model source)
    (stored : Stored heap p clock reference addresses buffer) (reset : Reset.Storage heap p)
    (args : Initialization.Arguments) (admissible : args.Admissible) :
    CStorage.Preserves heap (restarted heap p args) :=
  InitializationStorage.restarted model heap p .me reference.control.mode reset
    stored.control.kind stored.mode_loaded args admissible

end Rumoca.FMI3.MENumericalHistory

namespace Rumoca.FMI3.MEFailure
open CMemory

theorem Prepares.storage {input : Option (BitVec 64)} (prepared : Prepares input heap after buffer) :
    CStorage.Preserves heap after := by
  cases input with
  | none => cases prepared; exact .refl heap
  | some bits => exact CStorage.store_preserves prepared

end Rumoca.FMI3.MEFailure
end
