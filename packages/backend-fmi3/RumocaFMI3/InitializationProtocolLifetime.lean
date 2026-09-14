import RumocaFMI3.InitializationProtocolHistory
import RumocaFMI3.InitializationAccessStorage

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory CCalls.Events

/-- The existing actual factory's initialized-object result supplies the
protocol's default state and every reset/entry storage cell. -/
theorem Stored.created
    (initialized : InstanceInitialization.Initialized heap p kind environment logger logging) :
    Stored heap p kind State.reset :=
  ⟨initialized.access_instance Binary64.positiveZero initialized.model,
    initialized.storage.toStorage, trivial⟩

def Phase.Finished : Phase → Prop
  | .initialized _ | .failed => True
  | _ => False

theorem Phase.can_finish (kind : Kind) (phase : Phase) (finished : phase.Finished) :
    LifecycleRelease.CanFinish kind (phase.mode kind) := by
  cases phase with
  | instantiated | initializing args => exact False.elim finished
  | failed => exact Or.inr rfl
  | initialized args =>
    apply Or.inl
    cases kind <;> simp [Phase.mode, Reference.Allowed, me_initialization, cs_initialization]

/-- A finished initialization protocol releases the same owned slot. The
mode, metadata and reservation at release come from the original ownership
and the completed raw calls, including all prior rejected accesses/resets. -/
theorem Completed.release [interface : CInterface] {program : Program Invocation}
    (objects : Objects) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) {owners : SlotOwners.State objects.capacity}
    (contract : ExecutionContract model program objects retained owners original literals
      (objects.instances.index slot.val) buffers kind)
    (reference : ReferenceTrace kind state actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original (objects.instances.index slot.val) buffers)
    (invariant : Invariant program objects retained owners original literals heap (objects.instances.index slot.val) kind state)
    (executed : Completed program (objects.instances.index slot.val) buffers heap actions observed after checkpoints)
    (finished : final.phase.Finished)
    (termination : Termination.ReleaseContract objects program tag)
    (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩)))
    (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val)) :
    LifecycleRelease.Released objects program tag after slot owners owner kind (final.phase.mode kind) := by
  obtain ⟨_, _, finalInvariant, _, retains, _⟩ := executed.correct contract reference prepared invariant
  apply LifecycleRelease.finish_correct objects program tag termination release flags after slot kind _ owners owner
    finalInvariant.stored.instanceStored.kind finalInvariant.stored.instanceStored.mode
    (final.phase.can_finish kind finished) finalInvariant.ownership owned
  simpa only [load, retains "slot" (by decide)] using metadata

end Rumoca.FMI3.InitializationProtocol
end
