import RumocaFMI3.CompletedContract

noncomputable section
namespace Rumoca.FMI3.CompletedCalls
open CTree CMemory CBody StaticFactory CLiteral.Interface

theorem bounds_stored (clockStored : HistoryProofs.Stored heap p clock)
    (historyStored : Time.Represents history clock)
    (stopDefined : load heap (p.member "stopDefined") = some (boolean history.window.stopTime.isSome))
    (stopValue : ∀ stop, history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop))
    (event terminate : Address) (hne : event.block ≠ p.block) (hnt : terminate.block ≠ p.block) :
    TimeCalls.Bounds (HistoryBodies.completedHeap heap p event terminate clock) p
      history.completed.window clock.completed.minimum := by
  have frame (name : String) (last : name ≠ "lastCompleted") (minimum : name ≠ "timeMin") :
      HistoryBodies.completedHeap heap p event terminate clock (p.member name) = heap (p.member name) :=
    HistoryBodies.completed_frame heap p event terminate (p.member name) clock
      (by simpa using last) (by simpa using minimum)
      (HistoryBodies.field_ne_output p event name hne) (HistoryBodies.field_ne_output p terminate name hnt)
  refine ⟨(Time.completed_represents historyStored).minimum,
    HistoryProofs.load_cell (HistoryBodies.completed_stored clockStored event terminate hne hnt).minimum,
    ?_, ?_⟩
  · simpa only [load, frame "stopDefined" (by decide) (by decide)] using stopDefined
  · intro stop selected
    simpa only [load, frame "stop" (by decide) (by decide)] using stopValue stop selected

/-- The actual complete public call implements the positional completion
history, writes both false flags and retains the model and optional stop.
Caller outputs may alias each other; they lie outside the instance block. -/
theorem history_call [interface : CInterface] (program : CCalls.Events.Program E)
    (quiet : QuietContract program) (heap : Heap) (p event terminate : Address) (flag : Bool)
    (clock : Time.Clock) (history : Time.History) (state : ModelExchange.State)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (clockStored : HistoryProofs.Stored heap p clock) (historyStored : Time.Represents history clock)
    (stateStored : StateProofs.Represents heap p state)
    (stopDefined : load heap (p.member "stopDefined") = some (boolean history.window.stopTime.isSome))
    (stopValue : ∀ stop, history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop))
    (he : HistoryBodies.BoolWritable heap event) (ht : HistoryBodies.BoolWritable heap terminate)
    (hne : event.block ≠ p.block) (hnt : terminate.block ≠ p.block) :
    let after := HistoryBodies.completedHeap heap p event terminate clock
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (some event) (some terminate) flag) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) ∧
    HistoryProofs.Stored after p clock.completed ∧ Time.Represents history.completed clock.completed ∧
    StateProofs.Represents after p state ∧ load after (p.member "mode") = some (.integer 3) ∧
    load after event = some (boolean false) ∧ load after terminate = some (boolean false) ∧
    TimeCalls.Bounds after p history.completed.window clock.completed.minimum ∧
    (∀ query, query ≠ p.member "lastCompleted" → query ≠ p.member "timeMin" →
      query ≠ event → query ≠ terminate → after query = heap query) := by
  obtain ⟨eventAfter, terminateAfter⟩ := HistoryBodies.completed_outputs heap p event terminate clock hne hnt
  exact ⟨quiet.successful heap p event terminate flag clock hk hm clockStored he ht hne hnt,
    HistoryBodies.completed_stored clockStored event terminate hne hnt,
    Time.completed_represents historyStored, HistoryBodies.completed_model stateStored clock event terminate hne hnt,
    HistoryBodies.completed_mode heap p event terminate clock hm hne hnt, eventAfter, terminateAfter,
    bounds_stored clockStored historyStored stopDefined stopValue event terminate hne hnt,
    fun query last minimum eventOutside terminateOutside =>
      HistoryBodies.completed_frame heap p event terminate query clock last minimum eventOutside terminateOutside⟩

end Rumoca.FMI3.CompletedCalls
