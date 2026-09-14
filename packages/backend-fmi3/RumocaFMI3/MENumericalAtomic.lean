import RumocaFMI3.MENumericalHistory
import RumocaFMI3.MERelease

noncomputable section
namespace Rumoca.FMI3.MENumericalHistory
open CTree CMemory

/-- All numerical and importer writes use ordinary float storage. They
preserve every atomic reservation, including reservations in other slots. -/
theorem action_atomic (model : Solve.FMI3Model source)
    (stored : Stored heap p clock reference addresses buffer) (action : Action) :
    CAtomicBoolean.Preserves heap (action.after model heap p clock reference addresses buffer) := by
  cases action with
  | control command => exact MEHistory.action_atomic stored.control command
  | setState value =>
    obtain ⟨old, cell⟩ := stored.bufferCell
    exact (CAtomicBoolean.replace_nonatomic cell (by intro h; cases h) _).trans
      (CAtomicBoolean.replace_nonatomic (stored.write_buffer value).stateCell (by intro h; cases h) _)
  | getState | derivative =>
    obtain ⟨old, cell⟩ := stored.bufferCell
    exact CAtomicBoolean.replace_nonatomic cell (by intro h; cases h) _

theorem trace_atomic [CInterface] (program : CCalls.Events.Program E)
    (quiet : MEEnvironment.Quiet model program)
    (stored : Stored heap p clock reference addresses buffer)
    (admitted : ReferenceTrace reference actions final) :
    ∃ after finalClock,
      Calls program p addresses buffer heap actions (observations model reference actions) after ∧
      Stored after p finalClock final addresses buffer ∧
      CReadOnly.Preserves heap after ∧ CAtomicBoolean.Preserves heap after ∧
      (∀ q, Outside p addresses buffer q → after q = heap q) := by
  induction admitted generalizing heap clock with
  | nil => exact ⟨heap, clock, .nil, stored, .refl heap, .refl heap, fun _ _ => rfl⟩
  | cons accepted _ ih =>
    obtain ⟨prepared, called, storedAfter, output, controlOutputs, readonly, framed⟩ :=
      step program quiet stored _ accepted
    obtain ⟨after, finalClock, following, storedFinal, readonlyRest, atomicRest, framedRest⟩ := ih storedAfter
    exact ⟨after, finalClock, .cons prepared called output controlOutputs following, storedFinal,
      readonly.trans readonlyRest, (action_atomic model stored _).trans atomicRest,
      fun q outside => (framedRest q outside).trans (framed q outside)⟩

theorem Action.next_live (action : Action) (live : reference.control.Live) :
    (action.next reference).control.Live := by
  cases action with
  | control command => exact command.next_live live
  | setState _ | getState | derivative => exact live

theorem ReferenceTrace.live (admitted : ReferenceTrace reference actions final)
    (live : reference.control.Live) : final.control.Live := by
  induction admitted with
  | nil => exact live
  | cons _ _ ih => exact ih (Action.next_live _ live)

theorem Stored.slot_outside (stored : Stored heap p clock reference addresses buffer) :
    Outside p addresses buffer (p.member "slot") :=
  ⟨MEHistory.slot_outside stored.control.outside,
    Ne.symm (HistoryBodies.state_ne_field p "slot"), stored.field_ne_buffer "slot"⟩

end Rumoca.FMI3.MENumericalHistory
end
