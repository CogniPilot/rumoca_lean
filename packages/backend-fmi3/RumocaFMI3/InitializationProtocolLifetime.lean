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

/-- FMI 3.0.2 §2.3.1 admits fmi3FreeInstance in every state of a created
instance. Without a preceding fmi3Terminate, the actual release call only
discharges the lease; every other cell, including the mode, is retained. -/
def freedHeap (heap : Heap) (objects : Objects) (slot : Fin objects.capacity) : Heap :=
  replace heap (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)

structure Freed [CInterface] (objects : Objects) (program : Program E)
    (tag : CAtomicBoolean.Calls.Event → E) (heap : Heap) (slot : Fin objects.capacity)
    (owners : SlotOwners.State objects.capacity) (owner : Nat) : Prop where
  discharged : SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none)
  ownersAfter : SlotOwners.Represents objects.flagsBlock (freedHeap heap objects slot) (SlotOwners.update owners slot none)
  freed : ∀ behavior, (machine program).Behaves
    (.calling StaticRelease.function.signature.name [.pointer (some (objects.instances.index slot.val))] heap .done) behavior ↔
    behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, freedHeap heap objects slot⟩
  frame : ∀ q, q ≠ AtomicSlots.address objects.flagsBlock slot → freedHeap heap objects slot q = heap q

theorem freed_correct [interface : CInterface] (objects : Objects) (program : Program E)
    (tag : CAtomicBoolean.Calls.Event → E) (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩)))
    (heap : Heap) (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners) (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val)) :
    Freed objects program tag heap slot owners owner := by
  obtain ⟨discharged, representedAfter, _, framed, freed⟩ := StaticRelease.release_owned program tag heap
    objects.instances objects.flagsBlock owners slot owner release flags represented owned metadata
  exact ⟨discharged, representedAfter, freed, framed⟩

/-- A finished initialization protocol releases the same owned slot. The
mode, metadata and reservation at release come from the original ownership
and the completed raw calls, including all prior rejected accesses/resets. -/
theorem Completed.release [interface : CInterface] {program : Program Invocation}
    (objects : Objects) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (slot : Fin objects.capacity) {owners : SlotOwners.State objects.capacity} {readers : ReadBank}
    (contract : ExecutionContract model program objects retained owners original literals
      (objects.instances.index slot.val) buffers kind readers)
    (reference : ReferenceTrace kind state actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original (objects.instances.index slot.val) buffers readers)
    (invariant : Invariant program objects retained owners original literals heap (objects.instances.index slot.val) kind state readers)
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
  simpa only [load, retains.fields "slot" (by decide) (by decide)] using metadata

end Rumoca.FMI3.InitializationProtocol
end

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory

/-- Every cell of another instance record lies in the static pool, outside
this instance's record and apart from its lease flag. -/
theorem other_instance (objects : Objects) {slot other : Fin objects.capacity} (different : other ≠ slot)
    (inside : (objects.instances.index other.val).InRecord q) :
    q.block = objects.instances.block ∧ ¬ (objects.instances.index slot.val).InRecord q ∧
      q ≠ AtomicSlots.address objects.flagsBlock slot := by
  refine ⟨inside.1, fun mine => Address.records_separate objects.instances other.val slot.val
    (fun same => different (Fin.ext same)) inside mine rfl, ?_⟩
  intro same
  subst same
  exact objects.separate inside.1.symm

end Rumoca.FMI3.InitializationProtocol
end

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory

/-- Host ownership of caller cells: every cell an initialization action may
write lies outside the static instance pool. -/
def Action.PoolSeparate (objects : Objects) (action : Action) : Prop :=
  ∀ q, ¬ action.Outside q → q.block ≠ objects.instances.block

/-- Cells of another instance record are untouched by an owned
initialization segment of this instance. -/
theorem untouched_other (objects : Objects) {slot other : Fin objects.capacity} (different : other ≠ slot)
    (separate : buffers.Separate (objects.instances.index slot.val))
    (owned : ∀ action ∈ actions, action.PoolSeparate objects)
    (inside : (objects.instances.index other.val).InRecord q) :
    Untouched (objects.instances.index slot.val) buffers actions q := by
  obtain ⟨pooled, notRecord, _⟩ := other_instance objects different inside
  refine ⟨notRecord, Float64Access.instance_outside separate pooled, ?_⟩
  intro action member
  exact Classical.byContradiction fun touched => owned action member q touched pooled

end Rumoca.FMI3.InitializationProtocol
end
