import RumocaFMI3.AtomicSlots
import RumocaC.AtomicFrame

/-! Logical ownership of permanently allocated instance slots. An owner is a
ghost lease identifier, not a native thread ID or an extra FMI parameter.
Releasing a slot requires the current lease. Native handle validity and fresh
lease assignment across full invocation histories remain separate contracts. -/
namespace Rumoca.FMI3.SlotOwners
open CMemory

abbrev State (capacity : Nat) := Fin capacity → Option Nat

variable {capacity : Nat} {state : State capacity} {slot : Fin capacity}

def occupied (state : State capacity) : StaticSlots.State capacity := fun slot => (state slot).isSome

def update (state : State capacity) (slot : Fin capacity) (owner : Option Nat) : State capacity :=
  fun other => if other = slot then owner else state other

def reserve (state : State capacity) (slot : Fin capacity) (owner : Nat) : Option (State capacity) :=
  if state slot = none then some (update state slot (some owner)) else none

def release (state : State capacity) (slot : Fin capacity) (owner : Nat) : Option (State capacity) :=
  if state slot = some owner then some (update state slot none) else none

def Represents (block : Nat) (heap : Heap) (state : State capacity) : Prop :=
  AtomicSlots.Represents block heap (occupied state)

theorem occupied_update (state : State capacity) (slot : Fin capacity) (owner : Option Nat) :
    occupied (update state slot owner) = StaticSlots.update (occupied state) slot owner.isSome := by
  funext other
  by_cases same : other = slot <;> simp [occupied, update, StaticSlots.update, same]

theorem reserve_iff : reserve state slot owner = some after ↔
    state slot = none ∧ after = update state slot (some owner) := by
  by_cases vacant : state slot = none <;> simp [reserve, vacant, eq_comm]

theorem release_iff : release state slot owner = some after ↔
    state slot = some owner ∧ after = update state slot none := by
  by_cases owned : state slot = some owner <;> simp [release, owned, eq_comm]

theorem reserve_refines (reserved : reserve before slot owner = some after) :
    StaticSlots.reserve (occupied before) slot = some (occupied after) := by
  obtain ⟨vacant, rfl⟩ := reserve_iff.mp reserved
  simp [StaticSlots.reserve, occupied_update, occupied, vacant]

theorem release_refines (released : release before slot owner = some after) :
    StaticSlots.release (occupied before) slot = some (occupied after) := by
  obtain ⟨owned, rfl⟩ := release_iff.mp released
  simp [StaticSlots.release, occupied_update, occupied, owned]

theorem only_owner_releases (owned : before slot = some owner) (different : other ≠ owner) :
    release before slot other = none := by
  simp [release, owned, Ne.symm different]

theorem reserved_owner (reserved : reserve before slot owner = some after) : after slot = some owner := by
  rw [(reserve_iff.mp reserved).2]
  simp [update]

theorem reserved_excludes (reserved : reserve before slot owner = some after) (other : Nat) :
    reserve after slot other = none := by simp [reserve, reserved_owner reserved]

theorem reserve_frame (reserved : reserve before slot owner = some after) (different : other ≠ slot) :
    after other = before other := by rw [(reserve_iff.mp reserved).2]; simp [update, different]

theorem release_frame (released : release before slot owner = some after) (different : other ≠ slot) :
    after other = before other := by rw [(release_iff.mp released).2]; simp [update, different]

theorem initialized (heap : Heap) (block capacity : Nat) :
    Represents block (CAtomicBoolean.initial heap block capacity) (fun _ : Fin capacity => none) :=
  AtomicSlots.initialized heap block capacity

/-- An exchange which observed vacancy establishes the selected ghost lease;
the other slots retain their owners. The effect is the actual atomic operation. -/
theorem exchange_reserves (represented : Represents block before state)
    (step : CAtomicBoolean.exchange before (AtomicSlots.address block slot) true = some (false, after))
    (owner : Nat) :
    reserve state slot owner = some (update state slot (some owner)) ∧
      Represents block after (update state slot (some owner)) := by
  have effect := AtomicSlots.exchanged represented step
  have vacant : state slot = none := by
    cases stored : state slot <;> simp [occupied, stored] at effect
    rfl
  refine ⟨by simp [reserve, vacant], ?_⟩
  unfold Represents
  rw [occupied_update]
  exact effect.2

/-- A busy exchange cannot steal an existing lease, including when calls
from different host threads are interleaved. -/
theorem exchange_busy (represented : Represents block before state)
    (step : CAtomicBoolean.exchange before (AtomicSlots.address block slot) true = some (true, after)) :
    after = before ∧ Represents block after state := by
  have same := CAtomicBoolean.exchange_same (CAtomicBoolean.exchange_iff.mp step).1
  have heaps : after = before := congrArg Prod.snd (Option.some.inj (step.symm.trans same))
  exact ⟨heaps, by rw [heaps]; exact represented⟩

theorem write_releases (represented : Represents block before state)
    (owned : state slot = some owner)
    (step : CAtomicBoolean.write before (AtomicSlots.address block slot) false = some after) :
    release state slot owner = some (update state slot none) ∧ Represents block after (update state slot none) := by
  obtain ⟨observed, exchanged⟩ := CAtomicBoolean.write_as_exchange.mp step
  have effect := AtomicSlots.exchanged represented exchanged
  refine ⟨by simp [release, owned], ?_⟩
  unfold Represents
  rw [occupied_update]
  exact effect.2

theorem ordinary_preserves (represented : Represents block before state)
    (preserved : CAtomicBoolean.Preserves before after) : Represents block after state :=
  fun slot => preserved _ _ (represented slot)

variable [interface : CInterface]

theorem internal_preserves (represented : Represents block (CReadOnly.typedHeap before) owners)
    (program : CCalls.Events.Program E) (step : CCalls.Events.internalNext program before = some after) :
    Represents block (CReadOnly.typedHeap after) owners :=
  ordinary_preserves represented (CAtomicBoolean.internal_preserves program step)

end Rumoca.FMI3.SlotOwners
