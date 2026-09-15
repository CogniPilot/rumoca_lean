import RumocaFMI3.MEMixedProgress

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CMemory CCalls.Events

/-- The heap precedes the pending action. Only completed actions contribute
returned observations and initialization-exit checkpoints. -/
structure StopRecord where
  done : List Action
  pending : Action
  rest : List Action
  observed : List (MENumericalHistory.Observation Invocation)
  epochs : List MENumericalRun.Epoch
  heap : Heap

def Interrupted [CInterface] (program : Program Invocation) (p : Address)
    (addresses : String → Address) (buffer : Address) (heap : Heap)
    (actions : List Action) (stop : StopRecord) : Prop :=
  actions = stop.done ++ stop.pending :: stop.rest ∧
  Completed program p addresses buffer heap stop.done stop.observed stop.heap stop.epochs ∧
  Faulted program p addresses buffer stop.heap stop.pending

variable [CInterface] {program : Program Invocation}

theorem Completed.stopped
    (completed : Completed program p addresses buffer heap done observed middle epochs)
    (stopped : Stopped program p addresses buffer middle rest) :
    Stopped program p addresses buffer heap (done ++ rest) := by
  induction completed with
  | nil => exact stopped
  | cons performed _ ih => exact .later performed (ih stopped)

theorem Interrupted.stopped
    (interrupted : Interrupted program p addresses buffer heap actions stop) :
    Stopped program p addresses buffer heap actions := by
  rw [interrupted.1]
  exact interrupted.2.1.stopped (.here interrupted.2.2)

theorem Stopped.interrupted (stopped : Stopped program p addresses buffer heap actions) :
    ∃ stop, Interrupted program p addresses buffer heap actions stop := by
  induction stopped with
  | @here heap action rest faulted =>
    exact ⟨⟨[], action, rest, [], [], heap⟩, rfl, .nil, faulted⟩
  | @later heap action observed middle epochs rest performed _ ih =>
    obtain ⟨stop, same, completed, faulted⟩ := ih
    refine ⟨⟨action :: stop.done, stop.pending, stop.rest, observed ++ stop.observed,
      epochs ++ stop.epochs, stop.heap⟩, ?_, .cons performed completed, faulted⟩
    simp only [List.cons_append, same]

theorem interrupted_iff :
    (∃ stop, Interrupted program p addresses buffer heap actions stop) ↔
      Stopped program p addresses buffer heap actions :=
  ⟨fun ⟨_, interrupted⟩ => interrupted.stopped, Stopped.interrupted⟩

omit [CInterface] in
theorem ReferenceTrace.split
    (trace : ReferenceTrace buffer before clock (left ++ right) final finalClock) :
    ∃ middle middleClock, ReferenceTrace buffer before clock left middle middleClock ∧
      ReferenceTrace buffer middle middleClock right final finalClock := by
  induction left generalizing before clock with
  | nil => exact ⟨before, clock, .nil, trace⟩
  | cons action rest ih =>
    cases trace with
    | cons allowed tail =>
      obtain ⟨middle, middleClock, first, last⟩ := ih tail
      exact ⟨middle, middleClock, .cons allowed first, last⟩

variable {model : Solve.FMI3Model source} {objects : StaticFactory.Objects}
  {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}

/-- A finite prefix inherits the same complete call contracts and every
returning callback branch. Its starting resources are explicit. -/
theorem Trace.take
    (certified : Trace model objects owners capability program p addresses buffer heap enabled before clock
      (left ++ right) final finalClock)
    (stored : MENumericalHistory.Stored heap p clock before addresses buffer)
    (reset : Reset.Storage heap p) (configured : capability.Configured heap p enabled)
    (owned : SlotOwners.Represents objects.flagsBlock heap owners)
    (admitted : ReferenceTrace buffer before clock left middle middleClock) :
    Trace model objects owners capability program p addresses buffer heap enabled before clock left middle middleClock := by
  induction admitted generalizing heap enabled with
  | nil => exact .nil stored reset configured owned
  | cons _ _ ih =>
    cases certified with
    | cons called returned following =>
      refine .cons called returned ?_
      intro observed after epochs outcome
      have post := returned observed after epochs outcome
      exact ih (following observed after epochs outcome) post.stored post.resetStorage post.configuration post.ownership

/-- The suffix certificate starts at the actual last returned heap; no
successful suffix or callback return is assumed. -/
theorem Trace.after_prefix
    (certified : Trace model objects owners capability program p addresses buffer heap enabled before clock
      (left ++ right) final finalClock)
    (admitted : ReferenceTrace buffer before clock left middle middleClock)
    (completed : Completed program p addresses buffer heap left observed after epochs) :
    Trace model objects owners capability program p addresses buffer after ((loggingUpdate left).getD enabled) middle middleClock right final finalClock := by
  induction admitted generalizing heap enabled observed after epochs with
  | nil => cases completed; exact certified
  | cons _ _ ih =>
    cases completed with
    | cons performed tail =>
      cases certified with
      | cons called _ following =>
        simpa only [loggingUpdate_cons_getD] using
          ih (following _ _ _ (called.returned performed)) tail

end Rumoca.FMI3.MEMixedRun
end
