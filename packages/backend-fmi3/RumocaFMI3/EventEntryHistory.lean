import RumocaFMI3.EventEntryContract

noncomputable section
namespace Rumoca.FMI3.EventEntry
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface

/-- Event entry writes its two history fields and mode; continuous entry
only writes mode. Unrelated nested fields and neighboring instances are retained. -/
theorem frame (entry : Entry) (heap : Heap) (p query : Address) (clock : Time.Clock)
    (mode : query ≠ p.member "mode")
    (event : entry = .event → query ≠ p.member "eventTime" ∧ query ≠ p.member "timeMin") :
    afterHeap entry heap p clock query = heap query := by
  cases entry with
  | event => exact HistoryBodies.event_frame heap p query clock (event rfl).1 (event rfl).2 mode
  | continuous => exact LifecycleBodies.write_frame heap p query .continuous mode

theorem stored (entry : Entry) (clockStored : HistoryProofs.Stored heap p clock) :
    HistoryProofs.Stored (afterHeap entry heap p clock) p (afterClock entry clock) := by
  cases entry with
  | event => exact HistoryBodies.event_stored clockStored
  | continuous => exact LifecycleBodies.write_history clockStored .continuous

theorem represents (entry : Entry) (historyStored : Time.Represents history clock) :
    Time.Represents (afterHistory entry history) (afterClock entry clock) := by
  cases entry with
  | event => exact Time.event_represents historyStored
  | continuous => exact historyStored

theorem model_stored (entry : Entry) (stateStored : StateProofs.Represents heap p state) (clock : Time.Clock) :
    StateProofs.Represents (afterHeap entry heap p clock) p state := by
  cases entry with
  | event => exact HistoryBodies.event_model stateStored clock
  | continuous => exact LifecycleBodies.write_model stateStored .continuous

theorem mode_stored (entry : Entry) (heap : Heap) (p : Address) (clock : Time.Clock) :
    afterHeap entry heap p clock (p.member "mode") =
      some ⟨.int32, true, some (.integer entry.after.code)⟩ := by
  cases entry <;> simp [afterHeap, Entry.after, HistoryBodies.eventHeap, LifecycleBodies.writeMode, Mode.code]

theorem bounds_stored (entry : Entry) (clockStored : HistoryProofs.Stored heap p clock)
    (historyStored : Time.Represents history clock)
    (stopDefined : load heap (p.member "stopDefined") = some (boolean history.window.stopTime.isSome))
    (stopValue : ∀ stop, history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop)) :
    TimeCalls.Bounds (afterHeap entry heap p clock) p (afterHistory entry history).window
      (afterClock entry clock).minimum := by
  have stopSame : (afterHistory entry history).window.stopTime = history.window.stopTime := by
    cases entry <;> rfl
  refine ⟨(represents entry historyStored).minimum,
    HistoryProofs.load_cell (stored entry clockStored).minimum, ?_, ?_⟩
  · simpa only [stopSame, load, frame entry heap p (p.member "stopDefined") clock
      (by simp) (by intro _; simp)] using stopDefined
  · intro stop selected
    rw [stopSame] at selected
    simpa only [load, frame entry heap p (p.member "stop") clock
      (by simp) (by intro _; simp)] using stopValue stop selected

theorem history_call [interface : CInterface] (entry : Entry) (program : CCalls.Events.Program E)
    (quiet : QuietContract entry program) (heap : Heap) (p : Address) (clock : Time.Clock)
    (history : Time.History) (state : ModelExchange.State)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer entry.before.code)⟩)
    (clockStored : HistoryProofs.Stored heap p clock) (historyStored : Time.Represents history clock)
    (stateStored : StateProofs.Represents heap p state)
    (stopDefined : load heap (p.member "stopDefined") = some (boolean history.window.stopTime.isSome))
    (stopValue : ∀ stop, history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop)) :
    let after := afterHeap entry heap p clock
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling (signature entry).name [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) ∧
    HistoryProofs.Stored after p (afterClock entry clock) ∧
    Time.Represents (afterHistory entry history) (afterClock entry clock) ∧
    StateProofs.Represents after p state ∧
    after (p.member "mode") = some ⟨.int32, true, some (.integer entry.after.code)⟩ ∧
    TimeCalls.Bounds after p (afterHistory entry history).window (afterClock entry clock).minimum ∧
    (∀ query, query ≠ p.member "mode" →
      (entry = .event → query ≠ p.member "eventTime" ∧ query ≠ p.member "timeMin") → after query = heap query) := by
  exact ⟨quiet.successful heap p clock hk hm (fun _ => clockStored), stored entry clockStored,
    represents entry historyStored, model_stored entry stateStored clock, mode_stored entry heap p clock,
    bounds_stored entry clockStored historyStored stopDefined stopValue,
    fun query mode event => frame entry heap p query clock mode event⟩

end Rumoca.FMI3.EventEntry
