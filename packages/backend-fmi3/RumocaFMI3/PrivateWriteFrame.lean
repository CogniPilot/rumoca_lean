import RumocaFMI3.ResourcePublication
import RumocaC.Subobjects
import RumocaC.WriteRegions

noncomputable section
namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat} {authority : State capacity}
  {publications : PublicationRegistry.State capacity} {slot other : Fin capacity}

/-- A resource-backed instance is separate from any private initializer slot,
including every nested member and tensor offset. The slot inequality follows
from current publication authority rather than a supplied address inequality. -/
theorem private_record_separate (linked : Linked authority publications)
    (privateEntry : publications slot = some ⟨lease, false⟩)
    (owned : authority other = some account) (instances : Nat)
    (left : (AtomicSlots.address instances other).InRecord a)
    (right : (AtomicSlots.address instances slot).InRecord b) : a ≠ b := by
  have vacant := private_vacant linked privateEntry
  have different : other ≠ slot := by
    intro same
    subst other
    rw [vacant] at owned
    contradiction
  have indices : other.val ≠ slot.val := fun same => different (Fin.ext same)
  apply Address.records_separate ⟨instances, [], 0⟩ other.val slot.val indices
  · simpa only [Address.index, Nat.zero_add, AtomicSlots.address] using left
  · simpa only [Address.index, Nat.zero_add, AtomicSlots.address] using right

/-- An actual successful store into a resource-backed instance preserves all
private initializer cells, including their values. Caller buffers and external
callbacks need separate confinement contracts; they are not implicitly covered. -/
theorem store_preserves_private (linked : Linked authority publications)
    (privateEntry : publications slot = some ⟨lease, false⟩)
    (owned : authority other = some account)
    (destination : (AtomicSlots.address instances other).InRecord address)
    (stored : store before address value = some after) :
    Set.EqOn before after {q | (AtomicSlots.address instances slot).InRecord q} := by
  intro query inside
  exact (store_frame before address value after stored query
    (private_record_separate linked privateEntry owned instances destination inside).symm).symm

end Rumoca.FMI3.InstanceAuthority

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable [CInterface] {capacity : Nat} {authority : State capacity}
  {publications : PublicationRegistry.State capacity} {slot : Fin capacity}

/-- A current computed internal write targets an instance with current
publication authority. Output buffers need their own separation contracts. -/
def OwnedWrites (authority : State capacity) (instances : Nat) (state : Typed.State) : Prop :=
  ∀ address, CWriteFootprint.current state = some address →
    ∃ other account, authority other = some account ∧
      (AtomicSlots.address instances other).InRecord address

theorem owned_writes_avoid_private (linked : Linked authority publications)
    (privateEntry : publications slot = some ⟨lease, false⟩)
    (writes : OwnedWrites authority instances state) :
    CWriteFootprint.Avoids {q | (AtomicSlots.address instances slot).InRecord q} state := by
  intro address selected inside
  obtain ⟨other, account, owned, destination⟩ := writes address selected
  exact private_record_separate linked privateEntry owned instances destination inside rfl

/-- All actual internal C transitions, including loop bodies and saved return
assignments, preserve the private initializer from current resource authority
and computed destinations. No resulting heap frame is supplied. -/
theorem internal_preserves_private (linked : Linked authority publications)
    (privateEntry : publications slot = some ⟨lease, false⟩)
    (writes : OwnedWrites authority instances state)
    (step : Events.internalNext program state = some following) :
    Set.EqOn (CReadOnly.typedHeap state) (CReadOnly.typedHeap following)
      {q | (AtomicSlots.address instances slot).InRecord q} :=
  CWriteFootprint.internal_region (owned_writes_avoid_private linked privateEntry writes) step

theorem event_preserves_private (linked : Linked authority publications)
    (privateEntry : publications slot = some ⟨lease, false⟩)
    (writes : OwnedWrites authority instances state)
    (foreign : CWriteFootprint.ForeignFrame
      {q | (AtomicSlots.address instances slot).InRecord q} program state)
    (step : Events.Step program state events following) :
    Set.EqOn (CReadOnly.typedHeap state) (CReadOnly.typedHeap following)
      {q | (AtomicSlots.address instances slot).InRecord q} :=
  CWriteFootprint.event_region (owned_writes_avoid_private linked privateEntry writes) foreign step

theorem concurrent_preserves_private (linked : Linked authority publications)
    (privateEntry : publications slot = some ⟨lease, false⟩)
    (writes : ∀ saved, before.threads thread = some saved →
      OwnedWrites authority instances (Concurrent.withHeap saved before.heap))
    (foreign : ∀ saved, before.threads thread = some saved →
      CWriteFootprint.ForeignFrame {q | (AtomicSlots.address instances slot).InRecord q}
        program (Concurrent.withHeap saved before.heap))
    (step : Concurrent.Step program before thread events after) :
    Set.EqOn before.heap after.heap {q | (AtomicSlots.address instances slot).InRecord q} :=
  CWriteFootprint.concurrent_region
    (fun saved found => owned_writes_avoid_private linked privateEntry (writes saved found)) foreign step

end Rumoca.FMI3.InstanceAuthority
