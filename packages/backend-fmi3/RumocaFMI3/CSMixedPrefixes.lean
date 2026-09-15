import RumocaFMI3.CSMixedRun

noncomputable section
namespace Rumoca.FMI3.CSMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

def Action.MayBlock : Action → Prop
  | .run (.step _ _) => True
  | .run (.restart _) => False
  | .logging request => request.failed = true

theorem ActionContract.faulted_kind [CInterface] {program : Program Invocation}
    (certified : ActionContract program p heap action returns blocked)
    (actual : Faulted program p heap action) : action.MayBlock := by
  cases actual with
  | run faulted => cases certified with
    | run called =>
      obtain ⟨request, outputs, same⟩ := called.faulted_step faulted
      cases same
      trivial
  | logging faulted => cases certified with
    | logging called =>
      rcases (called.behaviors _).mp faulted with ⟨_, _, _, _, impossible⟩ | ⟨blocked, _⟩
      · cases impossible
      · exact called.failure blocked

/-- An actual completed prefix derives its own reference state, statuses,
exact logging update and the continuation certificate for the remaining calls. -/
theorem Trace.after_prefix [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (certified : Trace header objects owners model capability program p buffers heap enabled before (left ++ rest) final statuses)
    (stored : CSRun.Stored model heap p buffers before)
    (configured : capability.Configured heap p enabled)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (completed : Completed program p heap left observed events middle) :
    ∃ current expected remaining,
      statuses = expected ++ remaining ∧ observed = expected.map Value.integer ∧
      ReferenceTrace header p buffers before left current expected ∧
      CSRun.Stored model middle p buffers current ∧
      capability.Configured middle p ((loggingUpdate left).getD enabled) ∧
      InitializationProtocol.Retention (loggingUpdate left) p heap middle ∧
      SlotOwners.Represents objects.flagsBlock middle owners ∧ CReadOnly.Preserves heap middle ∧
      (∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → middle q = heap q) ∧
      Trace header objects owners model capability program p buffers middle
        ((loggingUpdate left).getD enabled) current rest final remaining := by
  induction completed generalizing enabled before statuses with
  | nil => exact ⟨before, [], statuses, rfl, rfl, .nil, stored, configured, .refl _ _, represented,
      .refl _, (fun _ _ _ => rfl), certified⟩
  | cons performed _ ih => cases certified with
    | cons changed called returned following =>
      have outcome := called.returned performed
      have post := returned _ _ _ outcome
      obtain ⟨current, expected, remaining, same, values, reference, finalStored, finalConfig,
        retention, ownership, readonly, frame, continuation⟩ :=
        ih (following _ _ _ outcome) post.stored post.configuration post.ownership
      refine ⟨current, _ :: expected, remaining, ?_, ?_, .cons changed reference, finalStored, ?_,
        post.retention.trans retention, ownership, post.readonly.trans readonly,
        (fun q guarded outside => (frame q guarded outside).trans (post.frame q guarded outside)), ?_⟩
      · exact congrArg (List.cons _) same
      · exact congrArg₂ List.cons post.observed.1 values
      · simpa only [loggingUpdate_cons_getD] using finalConfig
      · simpa only [loggingUpdate_cons_getD] using continuation

/-- Expose the exact completed prefix and the actual blocked call. -/
theorem Stopped.decompose [CInterface] {program : Program Invocation}
    (stopped : Stopped program p heap actions) :
    ∃ left action rest observed events middle,
      actions = left ++ action :: rest ∧ Completed program p heap left observed events middle ∧
      Faulted program p middle action := by
  induction stopped with
  | here faulted => exact ⟨[], _, _, [], [], _, rfl, .nil, faulted⟩
  | later performed _ ih =>
    obtain ⟨left, action, rest, observed, events, middle, same, completed, faulted⟩ := ih
    exact ⟨_ :: left, action, rest, _ :: observed, _, middle,
      congrArg (List.cons _) same, .cons performed completed, faulted⟩

theorem Trace.stopped_prefix [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses)
    (stored : CSRun.Stored model heap p buffers before)
    (configured : capability.Configured heap p enabled)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (stopped : Stopped program p heap actions) :
    ∃ left action rest observed events middle current expected remaining,
      actions = left ++ action :: rest ∧ Completed program p heap left observed events middle ∧
      Faulted program p middle action ∧ action.MayBlock ∧ statuses = expected ++ remaining ∧
      observed = expected.map Value.integer ∧ ReferenceTrace header p buffers before left current expected ∧
      CSRun.Stored model middle p buffers current ∧
      capability.Configured middle p ((loggingUpdate left).getD enabled) ∧
      InitializationProtocol.Retention (loggingUpdate left) p heap middle ∧
      SlotOwners.Represents objects.flagsBlock middle owners ∧ CReadOnly.Preserves heap middle ∧
      (∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → middle q = heap q) := by
  obtain ⟨left, action, rest, observed, events, middle, same, completed, faulted⟩ := stopped.decompose
  have full := certified
  rw [same] at full
  obtain ⟨current, expected, remaining, statusEq, values, reference, nextStored, nextConfig,
    retention, ownership, readonly, frame, continuation⟩ :=
    full.after_prefix stored configured represented completed
  refine ⟨left, action, rest, observed, events, middle, current, expected, remaining,
    same, completed, faulted, ?_, statusEq, values, reference, nextStored, nextConfig,
    retention, ownership, readonly, frame⟩
  cases continuation with
  | cons _ called _ _ => exact called.faulted_kind faulted

/-- Reference transitions are retained for the entire actual returned history. -/
theorem Trace.reference_of_completed [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses)
    (completed : Completed program p heap actions observed events after) :
    ReferenceTrace header p buffers before actions final statuses := by
  induction completed generalizing enabled before final statuses with
  | nil => cases certified; exact .nil
  | cons performed _ ih => cases certified with
    | cons changed called _ following =>
      exact .cons changed (ih (following _ _ _ (called.returned performed)))

end Rumoca.FMI3.CSMixedRun
end
