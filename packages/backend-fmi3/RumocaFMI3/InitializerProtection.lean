import RumocaFMI3.PrivateWriteFrame
import RumocaC.InitializerWrites
import RumocaFMI3.ClaimInitialization

namespace Rumoca.FMI3.PublicationRegistry
open CTree CMemory CCalls
variable {capacity : Nat} {publications : State capacity} {left right : Fin capacity}

/-- Different retained reservation identities imply separation of their whole
records, including nested fields and tensor offsets. -/
theorem reserved_records_separate
    (first : publications left = some firstEntry)
    (second : publications right = some secondEntry)
    (different : firstEntry.lease ≠ secondEntry.lease)
    (insideLeft : (AtomicSlots.address instances left).InRecord a)
    (insideRight : (AtomicSlots.address instances right).InRecord b) : a ≠ b := by
  have slots : left ≠ right := by
    intro same
    subst right
    exact different (congrArg Entry.lease (Option.some.inj (first.symm.trans second)))
  apply Address.records_separate ⟨instances, [], 0⟩ left.val right.val
    (fun same => slots (Fin.ext same))
  · simpa only [Address.index, AtomicSlots.address, Nat.zero_add] using insideLeft
  · simpa only [Address.index, AtomicSlots.address, Nat.zero_add] using insideRight

end Rumoca.FMI3.PublicationRegistry

namespace Rumoca.FMI3.StaticFactory.ClaimInitialization
open CTree CMemory CBody CCalls
variable [interface : CInterface] {capacity : Nat}
  {publications : PublicationRegistry.State capacity} {slot other : Fin capacity}

/-- An actual step of another claimed initializer preserves the tracked
private record. Current ledger identity and retained reservations derive record
separation; the actual initializer theorem supplies its exterior write frame.
Neither a successful completed initializer nor the resulting frame is assumed. -/
theorem step_preserves_other_private (program : Events.Program E)
    (unique : Host.Recording.Unique ledger)
    (active : ledger.active thread = some call)
    (tracked : ledger.active trackedThread = some trackedCall)
    (otherThread : thread ≠ trackedThread)
    (reserved : publications other = some ⟨call.serial, false⟩)
    (privateEntry : publications slot = some ⟨trackedCall.serial, false⟩)
    (scope : Scope env ⟨instances, [], 0⟩ flags capacity environment logger logging)
    (storage : InstanceSlot.Storage reference (AtomicSlots.address instances other))
    (bounded : other.val < 2^64)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (ready : Ready model kind env types ⟨instances, [], 0⟩ flags capacity other.val
      environment logger logging reference before)
    (step : Events.Step program before events after) :
    events = [] ∧
      Ready model kind env types ⟨instances, [], 0⟩ flags capacity other.val
        environment logger logging reference after ∧
      Set.EqOn (CReadOnly.typedHeap before) (CReadOnly.typedHeap after)
        {q | (AtomicSlots.address instances slot).InRecord q} := by
  have identities : call.serial ≠ trackedCall.serial :=
    fun same => otherThread (unique thread call trackedThread trackedCall active tracked same).1
  have typed : InstanceSlot.Storage reference ((⟨instances, [], 0⟩ : Address).index other.val) := by
    simpa only [Address.index, AtomicSlots.address, Nat.zero_add] using storage
  obtain ⟨silent, following, frame⟩ := step_with_frame program scope typed other.isLt bounded
    size pointer double handle ready step
  refine ⟨silent, following, ?_⟩
  intro query inside
  apply Eq.symm
  apply frame
  intro overlap
  have within : (AtomicSlots.address instances other).InRecord query := by
    simpa only [Address.index, AtomicSlots.address, Nat.zero_add] using overlap
  exact PublicationRegistry.reserved_records_separate reserved privateEntry identities within inside rfl

end Rumoca.FMI3.StaticFactory.ClaimInitialization

namespace Rumoca.FMI3.StaticFactory.ClaimInitialization
open CTree CMemory CCalls CAtomicScan.ConcurrentInvariant
variable [CInterface]

/-- Every possible memory destination in the real claimed initializer lies
inside its selected record. Scan return, guard and selection write only locals;
the certified initializer supplies the remaining store destinations. -/
theorem Ready.destination
    (ready : Ready model kind env types base flags capacity slot environment logger logging reference state)
    (selected : CWriteFootprint.current state = some address) : (base.index slot).InRecord address := by
  cases ready with
  | scan control agreement =>
    cases control <;>
      simp [CWriteFootprint.current, CWriteFootprint.loop, CWriteFootprint.saved,
        CWriteFootprint.target, tail, CAtomicScan.selected, caller] at selected
  | guard => simp [CWriteFootprint.current, CWriteFootprint.loop, StaticFactory.guard] at selected
  | select => simp [CWriteFootprint.current, CWriteFootprint.loop, initializeInstance, selectInstance] at selected
  | initializing control => exact control.destination selected

/-- A claimed initializer cannot enter another foreign call. This is derived
from its retained actual control, not from a callback-frame assumption. -/
theorem Ready.foreign_frame
    (ready : Ready model kind env types base flags capacity slot environment logger logging reference state) :
    CWriteFootprint.ForeignFrame region program state := by
  cases ready with
  | scan control agreement => cases control <;> trivial
  | guard | select => trivial
  | initializing control => exact control.foreign_frame

end Rumoca.FMI3.StaticFactory.ClaimInitialization
