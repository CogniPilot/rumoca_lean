import RumocaFMI3.InitializationProtocolHistory

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory CCalls.Events

structure StopRecord where
  done : List Action
  pending : Action
  rest : List Action
  observed : List (Float64Access.Observation Invocation)
  checkpoints : List Heap
  heap : Heap

/-- An observation view of the existing stopped initialization relation.
The pending call has no returned status, readback or exit checkpoint. -/
def Interrupted [CInterface] (program : Program Invocation) (p : Address) (buffers : Float64Buffers.Layout)
    (heap : Heap) (actions : List Action) (stop : StopRecord) : Prop :=
  actions = stop.done ++ stop.pending :: stop.rest ∧
  Completed program p buffers heap stop.done stop.observed stop.heap stop.checkpoints ∧
  stop.pending.Behaves program stop.heap p buffers (.wrong [])

variable [CInterface] {program : Program Invocation}

theorem Completed.stopped (completed : Completed program p buffers heap done observed middle checkpoints)
    (stopped : Stopped program p buffers middle rest) : Stopped program p buffers heap (done ++ rest) := by
  induction completed with
  | nil => exact stopped
  | cons called _ ih => exact .later called (ih stopped)

theorem Interrupted.stopped (interrupted : Interrupted program p buffers heap actions stop) :
    Stopped program p buffers heap actions := by
  rw [interrupted.1]
  exact interrupted.2.1.stopped (.here interrupted.2.2)

theorem Stopped.interrupted (stopped : Stopped program p buffers heap actions) :
    ∃ stop, Interrupted program p buffers heap actions stop := by
  induction stopped with
  | @here heap action rest called =>
    exact ⟨⟨[], action, rest, [], [], heap⟩, rfl, .nil, called⟩
  | @later middle rest heap action events status called _ ih =>
    obtain ⟨stop, same, completed, faulted⟩ := ih
    refine ⟨⟨action :: stop.done, stop.pending, stop.rest,
      ⟨events, status, action.readback middle buffers⟩ :: stop.observed,
      action.checkpoints middle ++ stop.checkpoints, stop.heap⟩, ?_, .cons called completed, faulted⟩
    simp only [List.cons_append, same]

theorem interrupted_iff : (∃ stop, Interrupted program p buffers heap actions stop) ↔
    Stopped program p buffers heap actions :=
  ⟨fun ⟨_, interrupted⟩ => interrupted.stopped, Stopped.interrupted⟩

omit [CInterface] in
theorem ReferenceTrace.split (trace : ReferenceTrace kind state (left ++ right) final) :
    ∃ middle, ReferenceTrace kind state left middle ∧ ReferenceTrace kind middle right final := by
  induction left generalizing state with
  | nil => exact ⟨state, .nil, trace⟩
  | cons action rest ih =>
    cases trace with
    | cons allowed tail =>
      obtain ⟨middle, prefixTrace, suffixTrace⟩ := ih tail
      exact ⟨middle, .cons allowed prefixTrace, suffixTrace⟩

end Rumoca.FMI3.InitializationProtocol
end
