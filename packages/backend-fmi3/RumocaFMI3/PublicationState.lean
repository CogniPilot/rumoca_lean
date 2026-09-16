import RumocaFMI3.ReservationRegistry

namespace Rumoca.FMI3.PublicationRegistry
open CMemory CCalls

/-- Proof-side publication bookkeeping. A published flag records an observed
factory completion; legal possession of the resulting handle is separate. -/
structure Entry where
  lease : Nat
  published : Bool
  deriving DecidableEq

abbrev State (capacity : Nat) := Fin capacity → Option Entry

def reservations (state : State capacity) : SlotOwners.State capacity :=
  fun slot => (state slot).map Entry.lease

/-- Follow the existing computed physical registry. Retain publication only
when the same reservation remains; a new reservation begins private. -/
def synchronize (state : State capacity) (owners : SlotOwners.State capacity) : State capacity :=
  fun slot => match owners slot with
  | none => none
  | some lease => match state slot with
    | some entry => if entry.lease = lease then some entry else some ⟨lease, false⟩
    | none => some ⟨lease, false⟩

def publish (state : State capacity) (slot : Fin capacity) (lease : Nat) : State capacity :=
  fun other => if other = slot then
    match state other with
    | some entry => if entry.lease = lease then some {entry with published := true} else some entry
    | none => none
  else state other

def Published (state : State capacity) (slot : Fin capacity) (lease : Nat) : Prop :=
  state slot = some ⟨lease, true⟩

theorem reservations_synchronize (state : State capacity) (owners : SlotOwners.State capacity) :
    reservations (synchronize state owners) = owners := by
  funext slot
  cases owned : owners slot with
  | none => simp [reservations, synchronize, owned]
  | some lease =>
    cases found : state slot with
    | none => simp [reservations, synchronize, owned, found]
    | some entry =>
      by_cases same : entry.lease = lease <;> simp [reservations, synchronize, owned, found, same]

theorem synchronize_reservations (state : State capacity) : synchronize state (reservations state) = state := by
  funext slot
  cases found : state slot <;> simp [synchronize, reservations, found]

theorem synchronize_new (vacant : state slot = none) (owned : owners slot = some lease) :
    synchronize state owners slot = some ⟨lease, false⟩ := by
  simp [synchronize, vacant, owned]

theorem synchronize_cleared (vacant : owners slot = none) : synchronize state owners slot = none := by
  simp [synchronize, vacant]

/-- Physical claims and clears cannot fabricate a publication observation. -/
theorem synchronize_published
    (published : Published (synchronize state owners) slot lease) : Published state slot lease := by
  unfold Published synchronize at published
  cases owned : owners slot with
  | none => simp [owned] at published
  | some owner =>
    cases found : state slot with
    | none => simp [owned, found] at published
    | some entry =>
      by_cases same : entry.lease = owner
      · simpa [owned, found, same, Published] using published
      · simp [owned, found, same, Entry.mk.injEq] at published

theorem reservations_publish (state : State capacity) (slot : Fin capacity) (lease : Nat) :
    reservations (publish state slot lease) = reservations state := by
  funext other
  by_cases same : other = slot
  · subst other
    cases found : state slot with
    | none => simp [reservations, publish, found]
    | some entry =>
      by_cases identity : entry.lease = lease <;> simp [reservations, publish, found, identity]
  · simp [reservations, publish, same]

theorem publish_owned (owned : state slot = some ⟨lease, previous⟩) :
    Published (publish state slot lease) slot lease := by
  simp [Published, publish, owned]

/-- A late completion for an old lease cannot publish a reused reservation. -/
theorem publish_wrong_lease (owned : state slot = some entry) (different : entry.lease ≠ lease) :
    publish state slot lease = state := by
  funext other
  by_cases same : other = slot
  · subst other
    simp [publish, owned, different]
  · simp [publish, same]

theorem publish_origin (published : Published (publish state selected origin) slot lease) :
    Published state slot lease ∨ slot = selected ∧ lease = origin ∧ reservations state slot = some lease := by
  by_cases same : slot = selected
  · subst selected
    cases found : state slot with
    | none => simp [Published, publish, found] at published
    | some entry =>
      by_cases identity : entry.lease = origin
      · have values : entry.lease = lease := by
          simpa [Published, publish, found, identity, Entry.mk.injEq] using published
        exact .inr ⟨rfl, values.symm.trans identity, by simp [reservations, found, values]⟩
      · exact .inl (by simpa [Published, publish, found, identity] using published)
  · exact .inl (by simpa [Published, publish, same] using published)

end Rumoca.FMI3.PublicationRegistry
