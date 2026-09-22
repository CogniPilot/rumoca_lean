import RumocaCore.GALEC.Elaboration.IteratorNames
import Parser.Token

/-! Fresh loop binders for the explicit repair profile. This does not define
general source shadowing policy. Non-iterator local barriers count as occupied
names even though iterator lookup deliberately returns none at such barriers.
Correct projection of source scopes remains a separate obligation. -/
namespace Rumoca.GALEC.Elaboration.Loops.Binder
open Elaboration _root_.Parser

inductive Fresh : IteratorNames bounds → String → Prop where
  | nil : Fresh .nil name
  | cons : name ≠ head → Fresh tail name → Fresh (.cons (bound := bound) head tail) name
  | blocked : name ≠ head → Fresh tail name → Fresh (.blocked head tail) name

def available : IteratorNames bounds → String → Bool
  | .nil, _ => true
  | .cons head tail, name => decide (name ≠ head) && available tail name
  | .blocked head tail, name => decide (name ≠ head) && available tail name

theorem available_iff (names : IteratorNames bounds) (name : String) :
    available names name = true ↔ Fresh names name := by
  induction names with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons head tail ih =>
    constructor
    · intro allowed
      have parts : name ≠ head ∧ Fresh tail name := by simpa [available, ih] using allowed
      exact .cons parts.1 parts.2
    · intro fresh
      cases fresh with
      | cons different tailFresh => simp [available, different, ih.mpr tailFresh]
  | blocked head tail ih =>
    constructor
    · intro allowed
      have parts : name ≠ head ∧ Fresh tail name := by simpa [available, ih] using allowed
      exact .blocked parts.1 parts.2
    · intro fresh
      cases fresh with
      | blocked different tailFresh => simp [available, different, ih.mpr tailFresh]

def read (names : IteratorNames bounds) : Token → Option String
  | .ident name => if available names name then some name else none
  | _ => none

inductive Accepts (names : IteratorNames bounds) : Token → String → Prop where
  | ident : Fresh names name → Accepts names (.ident name) name

theorem read_iff (names : IteratorNames bounds) (token : Token) (name : String) :
    read names token = some name ↔ Accepts names token name := by
  constructor
  · intro found
    cases token with
    | ident spelling =>
      change (if available names spelling then some spelling else none) = some name at found
      split at found
      · rename_i allowed
        cases Option.some.inj found
        exact .ident ((available_iff names _).mp allowed)
      · contradiction
    | number _ | literal _ => cases found
  · intro accepted
    cases accepted with
    | ident fresh => simp only [read, (available_iff _ _).mpr fresh, ↓reduceIte]

theorem fresh_lookup_none (fresh : Fresh names name) : names.lookup name = none := by
  induction fresh with
  | nil => rfl
  | cons different _ ih => simp [IteratorNames.lookup, different, ih]
  | blocked different _ ih => simp [IteratorNames.lookup, different, ih]

theorem barrier_rejected (tail : IteratorNames bounds) (name : String) :
    read (.blocked name tail) (.ident name) = none := by
  simp [read, available]

/-- Every previously resolved iterator remains the same outer slot, including
equal-extent nested loops. No assumption that lookup failure means freshness. -/
theorem outer_preserved (accepted : Accepts names token name)
    (resolved : IteratorNames.Resolves names other ⟨extent, ref⟩) (count : Nat) :
    IteratorNames.Resolves (.cons (bound := count) name names) other ⟨extent, .there ref⟩ := by
  cases accepted with
  | ident fresh =>
    apply IteratorNames.Resolves.there _ resolved
    intro same
    subst other
    have found := (IteratorNames.lookup_iff _ _ _).mpr resolved
    rw [fresh_lookup_none fresh] at found
    contradiction

end Rumoca.GALEC.Elaboration.Loops.Binder
