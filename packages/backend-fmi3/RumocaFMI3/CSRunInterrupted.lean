import RumocaFMI3.CSRunRecords

noncomputable section
namespace Rumoca.FMI3.CSRun
open CMemory CCalls.Events

/-- Observable completed prefix and the next, blocked action. The raw fault
retains any calls already performed within that action. -/
structure StopRecord (E : Type) where
  done : List Action
  pending : Action
  rest : List Action
  statuses : List Int
  events : List E
  calls : List (CallRecord E)
  heap : Heap

def Interrupted [CInterface] (program : Program E) (p : Address)
    (heap : Heap) (actions : List Action) (stop : StopRecord E) : Prop :=
  actions = stop.done ++ stop.pending :: stop.rest ∧
  Recorded program p heap stop.done stop.statuses stop.events stop.heap stop.calls ∧
  Faulted program p stop.heap stop.pending

variable [CInterface] {program : Program E}

theorem Recorded.stopped (completed : Recorded program p heap done statuses events middle calls)
    (stopped : Stopped program p middle rest) : Stopped program p heap (done ++ rest) := by
  induction completed with
  | nil => exact stopped
  | cons action _ ih => exact .later action.performed (ih stopped)

theorem Interrupted.stopped (interrupted : Interrupted program p heap actions stop) :
    Stopped program p heap actions := by
  rw [interrupted.1]
  exact interrupted.2.1.stopped (.here interrupted.2.2)

theorem Stopped.interrupted (stopped : Stopped program p heap actions) :
    ∃ stop, Interrupted program p heap actions stop := by
  induction stopped with
  | @here heap action rest faulted =>
    exact ⟨⟨[], action, rest, [], [], [], heap⟩, rfl, .nil, faulted⟩
  | @later heap action status events middle rest performed _ ih =>
    obtain ⟨stop, same, completed, faulted⟩ := ih
    obtain ⟨calls, recorded⟩ := performed.records
    refine ⟨⟨action :: stop.done, stop.pending, stop.rest, status :: stop.statuses,
      events ++ stop.events, calls ++ stop.calls, stop.heap⟩, ?_, .cons recorded completed, faulted⟩
    simp only [List.cons_append, same]

theorem interrupted_iff : (∃ stop, Interrupted program p heap actions stop) ↔ Stopped program p heap actions :=
  ⟨fun ⟨_, interrupted⟩ => interrupted.stopped, Stopped.interrupted⟩

omit [CInterface] in
/-- Splitting an admitted reference history does not assume anything about
the execution of its suffix. -/
theorem ReferenceTrace.split
    (trace : ReferenceTrace header p buffers before (left ++ right) final statuses) :
    ∃ middle prefixStatuses suffixStatuses,
      statuses = prefixStatuses ++ suffixStatuses ∧
      ReferenceTrace header p buffers before left middle prefixStatuses ∧
      ReferenceTrace header p buffers middle right final suffixStatuses := by
  induction left generalizing before statuses with
  | nil => exact ⟨before, [], statuses, rfl, .nil, trace⟩
  | cons action rest ih =>
    cases trace with
    | cons changed tail =>
      obtain ⟨middle, first, last, same, prefixTrace, suffixTrace⟩ := ih tail
      exact ⟨middle, _ :: first, last, by simp only [same, List.cons_append], .cons changed prefixTrace, suffixTrace⟩

end Rumoca.FMI3.CSRun
end
