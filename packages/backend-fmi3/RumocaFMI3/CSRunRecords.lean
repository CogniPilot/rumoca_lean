import RumocaFMI3.CSRunRaw

noncomputable section
namespace Rumoca.FMI3.CSRun
open CMemory StaticFactory CCalls.Events

/-- An actual public call's returned status, external events and final heap. -/
structure CallRecord (E : Type) where
  status : Int
  events : List E
  heap : Heap

/-- An observation view of one existing raw action. A restart retains each
public call, rather than only the last return value and final heap. -/
inductive RecordedAction [CInterface] (program : Program E) (p : Address) :
    Heap → Action → Int → List E → Heap → List (CallRecord E) → Prop where
  | step : Performed program p heap (.step request outputs) status events after →
      RecordedAction program p heap (.step request outputs) status events after [⟨status, events, after⟩]
  | restart :
      (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done)
        (.terminates resetEvents ⟨.integer resetStatus, resetHeap⟩) →
      (machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) resetHeap .done)
        (.terminates enterEvents ⟨.integer enterStatus, enteredHeap⟩) →
      (machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) enteredHeap .done)
        (.terminates exitEvents ⟨.integer exitStatus, after⟩) →
      RecordedAction program p heap (.restart args) exitStatus (resetEvents ++ enterEvents ++ exitEvents) after
        [⟨resetStatus, resetEvents, resetHeap⟩, ⟨enterStatus, enterEvents, enteredHeap⟩, ⟨exitStatus, exitEvents, after⟩]

inductive Recorded [CInterface] (program : Program E) (p : Address) :
    Heap → List Action → List Int → List E → Heap → List (CallRecord E) → Prop where
  | nil : Recorded program p heap [] [] [] heap []
  | cons : RecordedAction program p heap action status events middle records →
      Recorded program p middle rest statuses later after following →
      Recorded program p heap (action :: rest) (status :: statuses) (events ++ later) after (records ++ following)

variable [CInterface] {program : Program E}

theorem RecordedAction.performed (recorded : RecordedAction program p heap action status events after records) :
    Performed program p heap action status events after := by
  cases recorded with
  | step performed => exact performed
  | restart reset enter leave => exact .restart reset enter leave

theorem Performed.records (performed : Performed program p heap action status events after) :
    ∃ records, RecordedAction program p heap action status events after records := by
  cases performed with
  | step called => exact ⟨_, .step (.step called)⟩
  | restart reset enter leave => exact ⟨_, .restart reset enter leave⟩

theorem Recorded.completed (recorded : Recorded program p heap actions statuses events after records) :
    Completed program p heap actions statuses events after := by
  induction recorded with
  | nil => exact .nil
  | cons action _ ih => exact .cons action.performed ih

theorem Completed.records (completed : Completed program p heap actions statuses events after) :
    ∃ records, Recorded program p heap actions statuses events after records := by
  induction completed with
  | nil => exact ⟨[], .nil⟩
  | cons action _ ih =>
    obtain ⟨records, head⟩ := action.records
    obtain ⟨following, tail⟩ := ih
    exact ⟨records ++ following, .cons head tail⟩

/-- Adding the call records neither invents nor excludes a completed raw
execution. The reference/source model is absent from both sides. -/
theorem recorded_iff : (∃ records, Recorded program p heap actions statuses events after records) ↔
    Completed program p heap actions statuses events after :=
  ⟨fun ⟨_, recorded⟩ => recorded.completed, Completed.records⟩

def Action.callCount : Action → Nat
  | .step _ _ => 1
  | .restart _ => 3

theorem RecordedAction.length (recorded : RecordedAction program p heap action status events after records) :
    records.length = action.callCount := by cases recorded <;> rfl

theorem Recorded.length (recorded : Recorded program p heap actions statuses events after records) :
    records.length = (actions.map Action.callCount).sum := by
  induction recorded with
  | nil => rfl
  | cons action _ ih => simp only [List.length_append, action.length, ih, List.map_cons, List.sum_cons]

end Rumoca.FMI3.CSRun
end
