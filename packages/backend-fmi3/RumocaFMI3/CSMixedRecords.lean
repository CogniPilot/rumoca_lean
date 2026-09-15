import RumocaFMI3.CSMixedRun
import RumocaFMI3.CSRunRecordSemantics

noncomputable section
namespace Rumoca.FMI3.CSMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

/-- Uniform returned records reuse the C machine's result, including arbitrary
raw values. Numerical records embed their established integer-status view. -/
abbrev CallRecord := List Invocation × CBody.Result

def runRecord (record : CSRun.CallRecord Invocation) : CallRecord :=
  (record.events, ⟨.integer record.status, record.heap⟩)

inductive RecordedAction [CInterface] (program : Program Invocation) (p : Address) :
    Heap → Action → Value → List Invocation → Heap → List CallRecord → Prop where
  | run : CSRun.RecordedAction program p heap action status events after records →
      RecordedAction program p heap (.run action) (.integer status) events after (records.map runRecord)
  | logging : (machine program).Behaves
      (.calling (request.call p).1 (request.call p).2 heap .done) (.terminates events ⟨status, after⟩) →
      RecordedAction program p heap (.logging request) status events after [(events, ⟨status, after⟩)]

inductive Recorded [CInterface] (program : Program Invocation) (p : Address) :
    Heap → List Action → List Value → List Invocation → Heap → List CallRecord → Prop where
  | nil : Recorded program p heap [] [] [] heap []
  | cons : RecordedAction program p heap action status events middle records →
      Recorded program p middle rest statuses later after following →
      Recorded program p heap (action :: rest) (status :: statuses) (events ++ later) after (records ++ following)

theorem RecordedAction.performed [CInterface] {program : Program Invocation}
    (recorded : RecordedAction program p heap action status events after records) :
    Performed program p heap action status events after := by
  cases recorded with
  | run actual => exact .run actual.performed
  | logging actual => exact .logging actual

theorem Performed.records [CInterface] {program : Program Invocation}
    (performed : Performed program p heap action status events after) :
    ∃ records, RecordedAction program p heap action status events after records := by
  cases performed with
  | run actual =>
    obtain ⟨records, recorded⟩ := actual.records
    exact ⟨records.map runRecord, .run recorded⟩
  | logging actual => exact ⟨_, .logging actual⟩

theorem Recorded.completed [CInterface] {program : Program Invocation}
    (recorded : Recorded program p heap actions observed events after records) :
    Completed program p heap actions observed events after := by
  induction recorded with
  | nil => exact .nil
  | cons head _ ih => exact .cons head.performed ih

theorem Completed.records [CInterface] {program : Program Invocation}
    (completed : Completed program p heap actions observed events after) :
    ∃ records, Recorded program p heap actions observed events after records := by
  induction completed with
  | nil => exact ⟨[], .nil⟩
  | cons head _ ih =>
    obtain ⟨records, actual⟩ := head.records
    obtain ⟨following, tail⟩ := ih
    exact ⟨records ++ following, .cons actual tail⟩

/-- Recording each return neither invents nor excludes a raw completed trace. -/
theorem recorded_iff [CInterface] {program : Program Invocation} :
    (∃ records, Recorded program p heap actions observed events after records) ↔
      Completed program p heap actions observed events after :=
  ⟨fun ⟨_, recorded⟩ => recorded.completed, Completed.records⟩

theorem ActionContract.run_recorded [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {before next : CSRun.Reference}
    (certified : ActionContract program p heap (.run action) returns blocked)
    (changed : CSRun.Change header p buffers before action next expected)
    (returned : ∀ events value after, returns events value after →
      Returned objects owners model capability enabled p buffers heap after next (.run action) expected events value)
    (actual : CSRun.RecordedAction program p heap action observed events after records) :
    CSRun.SemanticAction model header p buffers heap before action observed records after next := by
  cases certified with
  | run called =>
    have outcome := (called.performed_status actual.performed).2
    have same := Value.integer.inj (returned _ _ _ ⟨rfl, outcome⟩).observed.1
    have change := changed
    rw [← same] at change
    apply called.recorded_correct change _ actual
    intro events after outcome
    have post := returned events _ after ⟨rfl, outcome⟩
    exact ⟨post.stored, by simpa only [same] using post.observed.2⟩

end Rumoca.FMI3.CSMixedRun
end
