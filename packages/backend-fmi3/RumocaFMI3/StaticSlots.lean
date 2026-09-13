import Mathlib.Data.Fin.Basic

/-! Reference ownership of a fixed set of instance slots. No object is
allocated or deallocated by these operations. Each reserve step is atomic in
this specification; a concurrent C implementation must prove that property
against its chosen synchronization primitives. -/
namespace Rumoca.FMI3.StaticSlots

abbrev State (capacity : Nat) := Fin capacity → Bool

def vacant : State capacity := fun _ => false

def update (state : State capacity) (slot : Fin capacity) (busy : Bool) : State capacity :=
  fun other => if other = slot then busy else state other

def reserve (state : State capacity) (slot : Fin capacity) : Option (State capacity) :=
  if state slot then none else some (update state slot true)

/-- Requires ownership of this live slot. The opaque FMI handle and native
storage correspondence are separate; stale handles are not made valid here. -/
def release (state : State capacity) (slot : Fin capacity) : Option (State capacity) :=
  if state slot then some (update state slot false) else none

variable {capacity : Nat} {state before middle after : State capacity}
  {slot a b : Fin capacity}

theorem reserve_iff : reserve state slot = some after ↔
    state slot = false ∧ after = update state slot true := by
  cases busy : state slot <;> simp [reserve, busy, eq_comm]

theorem reserve_busy (reserved : reserve state slot = some after) : after slot = true := by
  rw [(reserve_iff.mp reserved).2]
  simp [update]

theorem reserve_frame (reserved : reserve state slot = some after) (other : Fin capacity)
    (different : other ≠ slot) : after other = state other := by
  rw [(reserve_iff.mp reserved).2]
  simp [update, different]

theorem cannot_reserve_twice (reserved : reserve state slot = some after) :
    reserve after slot = none := by simp [reserve, reserve_busy reserved]

theorem consecutive_distinct (first : reserve before a = some middle)
    (second : reserve middle b = some after) : a ≠ b := by
  intro same
  subst b
  rw [cannot_reserve_twice first] at second
  contradiction

theorem full_iff : (∀ slot, reserve state slot = none) ↔ (∀ slot, state slot = true) := by
  constructor
  · intro full slot
    cases busy : state slot
    · simpa [reserve, busy] using full slot
    · rfl
  · intro full slot
    simp [reserve, full slot]

theorem release_iff : release state slot = some after ↔
    state slot = true ∧ after = update state slot false := by
  cases busy : state slot <;> simp [release, busy, eq_comm]

theorem release_vacant (released : release state slot = some after) : after slot = false := by
  rw [(release_iff.mp released).2]
  simp [update]

theorem release_frame (released : release state slot = some after) (other : Fin capacity)
    (different : other ≠ slot) : after other = state other := by
  rw [(release_iff.mp released).2]
  simp [update, different]

theorem release_after_reserve (reserved : reserve state slot = some after) :
    release after slot = some state := by
  rw [release, reserve_busy reserved]
  simp only [↓reduceIte, Option.some.injEq]
  funext other
  by_cases same : other = slot
  · subst other
    simpa [update] using (reserve_iff.mp reserved).1.symm
  · simp [update, same, reserve_frame reserved other same]

theorem reusable (released : release state slot = some after) :
    reserve after slot = some (update after slot true) := by
  simp [reserve, release_vacant released]

/-- Independent slot updates commute. This supports interleaving proofs; it
does not replace the still-required C atomicity/linearization theorem. -/
theorem update_commutes (state : State capacity) (a b : Fin capacity) (x y : Bool)
    (different : a ≠ b) :
    update (update state a x) b y = update (update state b y) a x := by
  funext slot
  by_cases ha : slot = a
  · subst slot
    simp [update, different]
  · by_cases hb : slot = b
    · subst slot
      simp [update, ha]
    · simp [update, ha, hb]

/-- Bounded serial search over fixed storage. A concurrent implementation
must refine atomic reservation, not assume that a prior read reserves a slot. -/
def findFree (state : State capacity) (start : Nat) : Nat → Option (Fin capacity)
  | 0 => none
  | fuel + 1 =>
    if inside : start < capacity then
      if state ⟨start, inside⟩ then findFree state (start + 1) fuel
      else some ⟨start, inside⟩
    else none

theorem findFree_sound (state : State capacity) (start fuel : Nat)
    (found : findFree state start fuel = some slot) :
    state slot = false ∧ start ≤ slot.val ∧ slot.val < start + fuel := by
  induction fuel generalizing start with
  | zero => simp [findFree] at found
  | succ fuel ih =>
    unfold findFree at found
    split at found
    · rename_i inside
      split at found
      · obtain ⟨free, lower, upper⟩ := ih (start + 1) found
        exact ⟨free, by omega, by omega⟩
      · rename_i available
        cases Option.some.inj found
        exact ⟨Bool.eq_false_iff.mpr available, Nat.le_refl _, by dsimp; omega⟩
    · contradiction

theorem findFree_none_iff (state : State capacity) (start fuel : Nat) :
    findFree state start fuel = none ↔
      ∀ slot : Fin capacity, start ≤ slot.val → slot.val < start + fuel → state slot = true := by
  induction fuel generalizing start with
  | zero => simp [findFree]; omega
  | succ fuel ih =>
    by_cases inside : start < capacity
    · cases busy : state ⟨start, inside⟩ with
      | false =>
        simp only [findFree, dif_pos inside, busy, Bool.false_eq_true, ↓reduceIte,
          Option.some_ne_none, false_iff, not_forall]
        exact ⟨⟨start, inside⟩, by simp [busy]⟩
      | true =>
        simp only [findFree, dif_pos inside, busy, ↓reduceIte, ih]
        constructor
        · intro rest slot lower upper
          by_cases first : slot.val = start
          · have same : slot = ⟨start, inside⟩ := Fin.ext first
            simpa [same] using busy
          · exact rest slot (by omega) (by omega)
        · intro all slot lower upper
          exact all slot (by omega) (by omega)
    · simp only [findFree, dif_neg inside, true_iff]
      intro slot lower _
      omega

theorem findFree_exhausted (state : State capacity) :
    findFree state 0 capacity = none ↔ ∀ slot, state slot = true := by
  rw [findFree_none_iff]
  constructor
  · intro full slot
    exact full slot (Nat.zero_le _) (by simpa only [Nat.zero_add] using slot.isLt)
  · intro full slot _ _
    exact full slot

theorem findFree_reserves (found : findFree state 0 capacity = some slot) :
    reserve state slot = some (update state slot true) := by
  simp [reserve, (findFree_sound state 0 capacity found).1]
end Rumoca.FMI3.StaticSlots
