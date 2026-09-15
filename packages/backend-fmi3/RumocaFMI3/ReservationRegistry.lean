import RumocaFMI3.ConcurrentSlotHistories

/-! A computed history of physical reservations. Clearing a flag removes its
reservation record; this records an effect and does not authorize a release.
The separate live-instance protocol must establish release authority. -/
namespace Rumoca.FMI3.ReservationRegistry
open CMemory
variable {capacity : Nat}

/-- Decode only an address of an element of this exact flag array. -/
def slotAt (block capacity : Nat) (address : Address) : Option (Fin capacity) :=
  if h : address.block = block ∧ address.members = [] ∧ address.offset < capacity
  then some ⟨address.offset, h.2.2⟩ else none

theorem slotAt_address (block : Nat) (slot : Fin capacity) :
    slotAt block capacity (AtomicSlots.address block slot) = some slot := by
  simp [slotAt, AtomicSlots.address, slot.isLt]

theorem slotAt_sound (decoded : slotAt block capacity address = some slot) :
    address = AtomicSlots.address block slot := by
  unfold slotAt at decoded
  split at decoded
  next h =>
    cases Option.some.inj decoded
    cases address
    simp only [AtomicSlots.address, Address.mk.injEq, and_true]
    exact ⟨h.1, h.2.1⟩
  next => contradiction

/-- Remove the physical reservation at the written address, if it belongs to
this pool. A write outside the pool leaves every record unchanged. -/
def clearAt (owners : SlotOwners.State capacity) (block : Nat) (address : Address) :
    SlotOwners.State capacity :=
  fun slot => if AtomicSlots.address block slot = address then none else owners slot

theorem clearAt_slot (owners : SlotOwners.State capacity) (slot : Fin capacity) :
    clearAt owners block (AtomicSlots.address block slot) = SlotOwners.update owners slot none := by
  funext other
  simp only [clearAt, SlotOwners.update, (AtomicSlots.address_injective block).eq_iff]

theorem clearAt_outside (owners : SlotOwners.State capacity)
    (outside : slotAt block capacity address = none) : clearAt owners block address = owners := by
  funext slot
  have different : AtomicSlots.address block slot ≠ address := by
    intro same
    rw [← same, slotAt_address] at outside
    contradiction
  simp [clearAt, different]

/-- An actual false store determines the next representation without assuming
that its caller owns a lease. Legal release is a strictly stronger property. -/
theorem clear_represents (represented : SlotOwners.Represents block before owners)
    (operation : CAtomicBoolean.write before address false = some after) :
    SlotOwners.Represents block after (clearAt owners block address) := by
  intro slot
  by_cases same : AtomicSlots.address block slot = address
  · rw [(CAtomicBoolean.write_iff.mp operation).2]
    simp [same, replace_at, SlotOwners.occupied, clearAt]
  · rw [CAtomicBoolean.write_frame operation same]
    simpa [SlotOwners.occupied, clearAt, same] using represented slot

/-- A real exchange updates the decoded slot with this invocation's serial
only when vacant; a busy exchange retains the previous reservation. -/
theorem claim_represents (represented : SlotOwners.Represents block before owners)
    (operation : CAtomicBoolean.exchange before (AtomicSlots.address block slot) true =
      some (busy, after)) (serial : Nat) :
    busy = SlotOwners.occupied owners slot ∧
      SlotOwners.Represents block after (ConcurrentSlots.claimOwners owners slot serial) := by
  have observed := (AtomicSlots.exchanged represented operation).1
  refine ⟨observed, ?_⟩
  cases busy with
  | false =>
    simpa [ConcurrentSlots.claimOwners, ← observed] using
      (SlotOwners.exchange_reserves represented operation serial).2
  | true =>
    simpa [ConcurrentSlots.claimOwners, ← observed] using
      (SlotOwners.exchange_busy represented operation).2

end Rumoca.FMI3.ReservationRegistry
