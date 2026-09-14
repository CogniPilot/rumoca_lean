import RumocaFMI3.TerminationEnvironment

noncomputable section
namespace Rumoca.FMI3.LifecycleRelease
open CTree CMemory CBody StaticFactory CCalls

/-- Release follows either an allowed termination call or an earlier Error
transition to Terminated. The latter must not call termination a second time. -/
def CanFinish (kind : Kind) (mode : Mode) : Prop :=
  Reference.Allowed .terminate kind mode ∨ mode = .terminated

def beforeRelease (heap : Heap) (p : Address) (mode : Mode) : Heap :=
  if mode = .terminated then heap else LifecycleBodies.writeMode heap p .terminated

def releasedHeap (heap : Heap) (objects : Objects) (slot : Fin objects.capacity) (mode : Mode) : Heap :=
  replace (beforeRelease heap (objects.instances.index slot.val) mode)
    (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)

/-- The common lifecycle suffix contains complete actual calls and returns
the original owner's reservation. It grants no future validity to the handle. -/
structure Released [CInterface] (objects : Objects) (program : Events.Program E)
    (tag : CAtomicBoolean.Calls.Event → E) (heap : Heap) (slot : Fin objects.capacity)
    (owners : SlotOwners.State objects.capacity) (owner : Nat) (kind : Kind) (mode : Mode) : Prop where
  modeAllowed : CanFinish kind mode
  terminated : mode ≠ .terminated → ∀ behavior, (Events.machine program).Behaves
    (.calling Termination.signature.name [.pointer (some (objects.instances.index slot.val))] heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, beforeRelease heap (objects.instances.index slot.val) mode⟩
  discharged : SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none)
  ownersAfter : SlotOwners.Represents objects.flagsBlock (releasedHeap heap objects slot mode) (SlotOwners.update owners slot none)
  freed : ∀ behavior, (Events.machine program).Behaves
    (.calling StaticRelease.function.signature.name [.pointer (some (objects.instances.index slot.val))]
      (beforeRelease heap (objects.instances.index slot.val) mode) .done) behavior ↔
    behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)]
      ⟨.void, releasedHeap heap objects slot mode⟩
  frame : ∀ q, q ≠ (objects.instances.index slot.val).member "mode" →
    q ≠ AtomicSlots.address objects.flagsBlock slot → releasedHeap heap objects slot mode q = heap q

/-- The shared suffix requires only interface cells and ownership; it does
not lower a model, select a solver or assume a successful release execution. -/
theorem finish_correct {E : Type} [interface : CInterface] (objects : Objects) (program : Events.Program E)
    (tag : CAtomicBoolean.Calls.Event → E) (finish : Termination.ReleaseContract objects program tag)
    (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩)))
    (heap : Heap) (slot : Fin objects.capacity) (kind : Kind) (mode : Mode)
    (owners : SlotOwners.State objects.capacity) (owner : Nat)
    (kindValue : load heap ((objects.instances.index slot.val).member "kind") = some (.integer kind.code))
    (modeValue : heap ((objects.instances.index slot.val).member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (ready : CanFinish kind mode) (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (owned : owners slot = some owner)
    (metadata : load heap ((objects.instances.index slot.val).member "slot") = some (.integer slot.val)) :
    Released objects program tag heap slot owners owner kind mode := by
  by_cases stopped : mode = .terminated
  · obtain ⟨discharged, representedAfter, _, framed, freed⟩ := StaticRelease.release_owned program tag heap
      objects.instances objects.flagsBlock owners slot owner release flags represented owned metadata
    refine ⟨ready, fun active => False.elim (active stopped), discharged, ?_, ?_, ?_⟩
    · simpa only [releasedHeap, beforeRelease, if_pos stopped] using representedAfter
    · intro behavior
      simpa only [releasedHeap, beforeRelease, if_pos stopped] using freed behavior
    · intro q _ notFlag
      simpa only [releasedHeap, beforeRelease, if_pos stopped] using framed q notFlag
  · have allowed : Reference.Allowed .terminate kind mode := ready.resolve_right stopped
    obtain ⟨terminated, discharged, representedAfter, framed, freed⟩ :=
      finish heap slot owners owner kind mode kindValue modeValue allowed represented owned metadata
    refine ⟨ready, ?_, discharged, ?_, ?_, ?_⟩
    · intro _ behavior
      simpa only [beforeRelease, if_neg stopped] using terminated behavior
    · simpa only [releasedHeap, beforeRelease, if_neg stopped] using representedAfter
    · intro behavior
      simpa only [releasedHeap, beforeRelease, if_neg stopped] using freed behavior
    · intro q notMode notFlag
      simpa only [releasedHeap, beforeRelease, if_neg stopped] using framed q notMode notFlag

end Rumoca.FMI3.LifecycleRelease
end
