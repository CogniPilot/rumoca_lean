import RumocaFMI3.CSMixedPrefixes
import RumocaFMI3.CSRunFinish

noncomputable section
namespace Rumoca.FMI3.CSMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

theorem Change.rehandle (changed : Change header p buffers before action after status) (q : Address) :
    Change header q buffers before action after status := by
  cases changed with
  | run changed => exact .run (changed.rehandle q)
  | logging => exact .logging

theorem ReferenceTrace.rehandle (trace : ReferenceTrace header p buffers before actions after statuses) (q : Address) :
    ReferenceTrace header q buffers before actions after statuses := by
  induction trace with
  | nil => exact .nil
  | cons changed _ ih => exact .cons (changed.rehandle q) ih

theorem Change.can_finish (changed : Change header p buffers before action after status)
    (ready : CSRun.CanFinish before.mode) : CSRun.CanFinish after.mode := by
  cases changed with
  | run changed => exact changed.can_finish ready
  | @logging request =>
    cases failed : request.failed with
    | false => simpa only [CSLoggingCalls.next, failed, Bool.false_eq_true, if_false] using ready
    | true => exact Or.inr (by simp only [CSLoggingCalls.next, failed, if_true])

theorem ReferenceTrace.can_finish (trace : ReferenceTrace header p buffers before actions after statuses)
    (ready : CSRun.CanFinish before.mode) : CSRun.CanFinish after.mode := by
  induction trace with
  | nil => exact ready
  | cons changed _ ih => exact ih (changed.can_finish ready)

/-- All returned branches retain the actual slot metadata and ownership used
by mode-appropriate termination and release. No later valid handle is granted. -/
theorem Trace.released [interface : CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {slot : Fin objects.capacity}
    (tag : CAtomicBoolean.Calls.Event → Invocation)
    (finish : Termination.ReleaseContract objects program tag) (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩)))
    (certified : Trace header objects owners model capability program (objects.instances.index slot.val) buffers
      heap enabled before actions final statuses)
    (completed : Completed program (objects.instances.index slot.val) heap actions observed events after)
    (ready : CSRun.CanFinish before.mode) (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val)) :
    CSRun.Released objects program tag after slot owners owner final.mode := by
  obtain ⟨_, stored, _, retained, ownership, _, _⟩ := certified.completed completed
  have metadataAfter : load after ((objects.instances.index slot.val).member "slot") = some (.integer slot.val) := by
    rw [load, retained.fields "slot" (by decide) (by decide)]
    exact metadata
  exact CSRun.finish_correct objects program tag finish release flags model after slot buffers final owners owner
    stored ((certified.reference_of_completed completed).can_finish ready) ownership owned metadataAfter

/-- Borrowed caller contents survive the complete returned history and the
actual release, under the original universal callback frame and write separation. -/
theorem Trace.released_frame [interface : CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {slot : Fin objects.capacity} {region : Address → Prop} {tag : CAtomicBoolean.Calls.Event → Invocation}
    (certified : Trace header objects owners model capability program (objects.instances.index slot.val) buffers
      heap enabled before actions final statuses)
    (completed : Completed program (objects.instances.index slot.val) heap actions observed events after)
    (released : CSRun.Released objects program tag after slot owners owner final.mode)
    (policy : capability.Requires (fun _ effect =>
      ∀ args before value after, effect.execute args before value after → ∀ q, region q → after q = before q)) :
    ∀ q, region q → CSRun.Outside (objects.instances.index slot.val) buffers q →
      q ≠ AtomicSlots.address objects.flagsBlock slot →
      CSRun.releasedHeap after objects slot final.mode q = heap q := by
  intro q inside outside notFlag
  exact (released.frame q (outside.field "mode") notFlag).trans
    (certified.callerFrame completed policy q inside outside)

end Rumoca.FMI3.CSMixedRun
end
