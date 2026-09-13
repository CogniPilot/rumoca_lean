import RumocaFMI3.TimeCalls
import RumocaFMI3.HistoryProofs

noncomputable section
namespace Rumoca.FMI3.TimeCalls
open CTree CMemory CBody StaticFactory
open Binary64 (toBits)

/-- The time write leaves every other instance cell, history bound, and
neighboring record unchanged. It does not advance the model state. -/
theorem frame (heap : Heap) (p query : Address) (bits : BitVec 64)
    (outside : query ≠ p.member "time") :
    StateProofs.written heap (p.member "time") bits query = heap query :=
  StateProofs.written_frame heap _ query bits outside

theorem bounds_after (stored : Bounds heap p window minimum) (bits : BitVec 64) :
    Bounds (StateProofs.written heap (p.member "time") bits) p window minimum := by
  refine ⟨stored.lower, ?_, ?_, ?_⟩
  · simpa only [load, frame heap p (p.member "timeMin") bits (by simp)] using stored.minimumValue
  · simpa only [load, frame heap p (p.member "stopDefined") bits (by simp)] using stored.stopDefined
  · intro stop present
    simpa only [load, frame heap p (p.member "stop") bits (by simp)] using stored.stopValue stop present

/-- A complete public call implements the independently specified trial-time
history transition. The model value is retained for the importer's subsequent
state update/evaluation; this is not a numerical integration theorem. -/
theorem history_call [interface : CInterface] (program : CCalls.Events.Program E)
    (quiet : QuietContract program) (heap : Heap) (p : Address) (clock : Time.Clock)
    (history : Time.History) (time : Binary64.Value) (state : ModelExchange.State)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (clockStored : HistoryProofs.Stored heap p clock) (historyStored : Time.Represents history clock)
    (stateStored : StateProofs.Represents heap p state)
    (stopDefined : load heap (p.member "stopDefined") = some (boolean history.window.stopTime.isSome))
    (stopValue : ∀ stop, history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop))
    (admissible : history.window.Admissible time) :
    let after := StateProofs.written heap (p.member "time") (toBits time).val
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (toBits time).val) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) ∧
    HistoryProofs.Stored after p (clock.setTime time) ∧
    Time.Represents (history.setTime time) (clock.setTime time) ∧
    StateProofs.Represents after p state ∧
    Bounds after p history.window clock.minimum ∧
    (∀ query, query ≠ p.member "time" → after query = heap query) := by
  have bounds : Bounds heap p history.window clock.minimum :=
    ⟨historyStored.minimum, HistoryProofs.load_cell clockStored.minimum, stopDefined, stopValue⟩
  refine ⟨quiet.successful heap p history.window clock.minimum time _ hk hm bounds clockStored.time admissible,
    HistoryProofs.write_time clockStored time, Time.setTime_represents historyStored admissible, ?_,
    bounds_after bounds _, fun query outside => frame heap p query _ outside⟩
  simpa only [StateProofs.Represents, load, TimeProofs.model_frame] using stateStored

end Rumoca.FMI3.TimeCalls
