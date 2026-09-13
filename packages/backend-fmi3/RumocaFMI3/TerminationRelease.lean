import RumocaFMI3.TerminationContract
import RumocaFMI3.StaticRelease

noncomputable section
namespace Rumoca.FMI3.Termination
open CTree CMemory StaticFactory

theorem lease_metadata (heap : Heap) (p : Address) :
    load (LifecycleBodies.writeMode heap p .terminated) (p.member "slot") =
      load heap (p.member "slot") := by
  simp only [load, LifecycleBodies.write_frame heap p (p.member "slot") .terminated (by simp)]

theorem lease_owners (objects : Objects) (heap : Heap) (slot : Fin objects.capacity)
    (owners : SlotOwners.State objects.capacity)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners) :
    SlotOwners.Represents objects.flagsBlock
      (LifecycleBodies.writeMode heap (objects.instances.index slot.val) .terminated) owners := by
  intro other
  have different : AtomicSlots.address objects.flagsBlock other ≠
      (objects.instances.index slot.val).member "mode" := by
    intro same
    exact objects.separate (congrArg Address.block same).symm
  rw [LifecycleBodies.write_frame _ _ _ _ different]
  exact represented other

/-- Complete termination/release observations and ownership discharge. The
input lease is a host obligation; all later flag and metadata facts are results. -/
def ReleaseContract [interface : CInterface] (objects : Objects)
    (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E) : Prop :=
      ∀ (heap : Heap) (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity)
        (owner : Nat) (kind : Kind) (mode : Mode),
      let p := objects.instances.index slot.val
      load heap (p.member "kind") = some (.integer kind.code) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
      Reference.Allowed .terminate kind mode →
      SlotOwners.Represents objects.flagsBlock heap owners → owners slot = some owner →
      load heap (p.member "slot") = some (.integer slot.val) →
      let terminated := LifecycleBodies.writeMode heap p .terminated
      let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
      SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
      SlotOwners.Represents objects.flagsBlock released (SlotOwners.update owners slot none) ∧
      (∀ query, query ≠ p.member "mode" → query ≠ AtomicSlots.address objects.flagsBlock slot →
        released query = heap query) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
        behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩)

/-- Termination's exact result supplies release's metadata and occupied flag.
The host owns the input lease; the theorem derives its discharge after both
actual calls, with no new post-termination ownership premise. -/
theorem terminate_release {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
      QuietContract program → StaticRelease.Bindings program tag →
      ReleaseContract objects program tag := by
  letI : CInterface := executionInterface objects literals
  intro program tag quiet bindings heap slot owners owner kind mode
  let p := objects.instances.index slot.val
  dsimp only
  intro hk hm allowed represented owned metadata
  obtain ⟨discharged, representedAfter, _, framed, freed⟩ := StaticRelease.release_owned program tag
    (LifecycleBodies.writeMode heap p .terminated) objects.instances objects.flagsBlock owners slot owner bindings rfl
    (lease_owners objects heap slot owners represented) owned ((lease_metadata heap p).trans metadata)
  refine ⟨quiet.successful heap p kind mode hk hm allowed, discharged, representedAfter, ?_, freed⟩
  intro query outsideMode outsideFlag
  rw [framed query outsideFlag]
  exact LifecycleBodies.write_frame heap p query .terminated outsideMode

end Rumoca.FMI3.Termination
