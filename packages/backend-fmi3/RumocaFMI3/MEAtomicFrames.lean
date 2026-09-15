import RumocaFMI3.MEHistory
import RumocaC.OutputAtomicFrame

noncomputable section
namespace Rumoca.FMI3.HistoryProofs
open CMemory

theorem write_atomic (found : heap (p.member name) = some (cell old)) (value : Binary64.Value) :
    CAtomicBoolean.Preserves heap (write heap p name value) :=
  CAtomicBoolean.replace_nonatomic found (by simp [cell]) _

theorem raise_atomic (found : heap (p.member name) = some (cell old))
    (current value : Binary64.Value) : CAtomicBoolean.Preserves heap (raiseHeap heap p name current value) := by
  unfold raiseHeap
  split
  · exact write_atomic found value
  · exact .refl heap

theorem event_atomic (stored : Stored heap p clock) : CAtomicBoolean.Preserves heap (eventHeap heap p clock) :=
  (write_atomic stored.eventTime clock.time).trans
    (raise_atomic (write_event stored clock.time).minimum clock.minimum clock.time)

theorem completed_atomic (stored : Stored heap p clock) :
    CAtomicBoolean.Preserves heap (completedHeap heap p clock) :=
  (write_atomic stored.minimum clock.eventTime).trans
    ((raise_atomic (write_minimum stored clock.eventTime).minimum clock.eventTime clock.lastCompleted).trans
      (write_atomic (raise_minimum (write_minimum stored clock.eventTime) clock.lastCompleted).lastCompleted clock.time))

end Rumoca.FMI3.HistoryProofs

namespace Rumoca.FMI3.MEHistory
open CTree CMemory

/-- Each control action preserves every pre-existing atomic cell. Ordinary
typed output buffers cannot alias atomic reservations, even in the same block. -/
theorem action_atomic (stored : Stored heap p clock reference model addresses) (action : Action) :
    CAtomicBoolean.Preserves heap (action.heap heap p clock addresses) := by
  cases action with
  | setTime time => exact HistoryProofs.write_atomic stored.clockStored.time time
  | enter entry =>
    cases entry with
    | continuous => exact CAtomicBoolean.replace_nonatomic stored.mode (by intro h; cases h) _
    | event =>
      have modeAfter : HistoryProofs.eventHeap heap p clock (p.member "mode") =
          some ⟨.int32, true, some (.integer reference.mode.code)⟩ := by
        rw [HistoryProofs.event_frame heap p (p.member "mode") clock (by simp) (by simp)]
        exact stored.mode
      exact (HistoryProofs.event_atomic stored.clockStored).trans
        (CAtomicBoolean.replace_nonatomic modeAfter (by intro h; cases h) _)
  | evaluateDiscrete => exact .refl heap
  | updateDiscrete =>
    apply COutputAssignments.after_atomic stored.buffers.writable
    intro entry member
    change entry ∈ DiscreteCalls.layouts.map (DiscreteCalls.output addresses) at member
    obtain ⟨layout, declared, rfl⟩ := List.mem_map.mp member
    simp only [DiscreteCalls.layouts, List.mem_cons, List.not_mem_nil, or_false] at declared
    rcases declared with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [DiscreteCalls.output]
  | completed _ =>
    have event : HistoryBodies.BoolWritable heap (addresses "discreteStatesNeedUpdate") :=
      stored.buffers ("discreteStatesNeedUpdate", .boolean) (by decide +kernel)
    have terminate : HistoryBodies.BoolWritable
        (HistoryBodies.zero heap (addresses "discreteStatesNeedUpdate")) (addresses "terminateSimulation") :=
      HistoryBodies.zero_writable
        (stored.buffers ("terminateSimulation", .boolean) (by decide +kernel)) _
    obtain ⟨oldEvent, event⟩ := event
    obtain ⟨oldTerminate, terminate⟩ := terminate
    exact (CAtomicBoolean.replace_nonatomic event (by intro h; cases h) _).trans
      ((CAtomicBoolean.replace_nonatomic terminate (by intro h; cases h) _).trans
        (HistoryProofs.completed_atomic (HistoryBodies.outputs_stored stored.clockStored _ _
          (stored.outside "discreteStatesNeedUpdate" (by decide +kernel))
          (stored.outside "terminateSimulation" (by decide +kernel)))))

/-- Derive exact public calls, the continued control/storage invariant,
all atomic reservations and the ordinary memory frame in one result. -/
theorem trace_atomic_frame [interface : CInterface] (program : CCalls.Events.Program E) (quiet : Quiet program)
    (stored : Stored heap p clock reference model addresses) (admitted : ReferenceTrace reference actions final) :
    ∃ after finalClock, Calls program p addresses heap actions after ∧
      Stored after p finalClock final model addresses ∧ CAtomicBoolean.Preserves heap after ∧
      (∀ query, Outside p addresses query → after query = heap query) := by
  induction admitted generalizing heap clock with
  | nil => exact ⟨heap, clock, .nil, stored, .refl heap, fun _ _ => rfl⟩
  | cons accepted _ ih =>
    obtain ⟨called, storedAfter, outputs⟩ := step program quiet stored _ accepted
    obtain ⟨after, finalClock, calledRest, storedFinal, atomic, framed⟩ := ih storedAfter
    refine ⟨after, finalClock, .cons called outputs calledRest, storedFinal,
      (action_atomic stored _).trans atomic, ?_⟩
    intro query outside
    exact (framed query outside).trans (action_frame _ heap p query clock addresses outside)

end Rumoca.FMI3.MEHistory
