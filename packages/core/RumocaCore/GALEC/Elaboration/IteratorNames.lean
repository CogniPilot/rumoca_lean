import RumocaCore.GALEC.IndexSyntax

/-! Core-owned name resolution metadata for bounded iterators. It decorates
the existing intrinsic iterator context without changing its representation.
The independent relation specifies lexical first-match lookup. A later source
profile may forbid shadowing; lookup must never skip a nearer binding merely
because an outer iterator has a more convenient extent. -/
namespace Rumoca.GALEC.Elaboration

inductive IteratorNames : List Nat → Type where
  | nil : IteratorNames []
  | cons (name : String) (tail : IteratorNames bounds) : IteratorNames (bound :: bounds)
  | blocked (name : String) (tail : IteratorNames bounds) : IteratorNames bounds

namespace IteratorNames

def lookup : IteratorNames bounds → String → Option (Σ bound, IteratorRef bounds bound)
  | .nil, _ => none
  | .cons (bound := bound) head tail, name =>
      if name = head then some ⟨bound, .here⟩
      else (lookup tail name).map fun ⟨extent, ref⟩ => ⟨extent, .there ref⟩
  | .blocked head tail, name => if name = head then none else lookup tail name

/-- Independent lexical binding judgment, not a call to the lookup function. -/
inductive Resolves : {bounds : List Nat} → IteratorNames bounds → String →
    (Σ bound, IteratorRef bounds bound) → Prop where
  | here : Resolves (.cons (bound := bound) name tail) name ⟨bound, .here⟩
  | there : name ≠ head → Resolves tail name ⟨extent, ref⟩ →
      Resolves (.cons (bound := bound) head tail) name ⟨extent, .there ref⟩
  | throughBlocked : name ≠ head → Resolves tail name entry →
      Resolves (.blocked head tail) name entry

theorem lookup_iff (names : IteratorNames bounds) (name : String)
    (entry : Σ bound, IteratorRef bounds bound) :
    names.lookup name = some entry ↔ Resolves names name entry := by
  induction names with
  | nil =>
    constructor
    · intro impossible; cases impossible
    · intro impossible; cases impossible
  | @cons bounds bound head tail ih =>
    by_cases same : name = head
    · subst name
      constructor
      · intro found
        simp [lookup] at found
        cases found
        exact .here
      · intro resolved
        cases resolved with
        | here => simp [lookup]
        | there different _ => exact False.elim (different rfl)
    · constructor
      · intro found
        simp only [lookup, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨⟨extent, ref⟩, inner, rfl⟩ := found
        exact .there same ((ih ⟨extent, ref⟩).mp inner)
      · intro resolved
        cases resolved with
        | here => exact False.elim (same rfl)
        | @there _ _ _ _ extent ref _ different inner =>
          simp only [lookup, if_neg same, Option.map_eq_some_iff]
          exact ⟨⟨extent, ref⟩, (ih ⟨extent, ref⟩).mpr inner, rfl⟩
  | blocked head tail ih =>
    by_cases same : name = head
    · subst name
      constructor
      · simp [lookup]
      · intro resolved
        cases resolved with
        | throughBlocked different _ => exact False.elim (different rfl)
    · simp only [lookup, if_neg same]
      constructor
      · intro found
        exact .throughBlocked same ((ih entry).mp found)
      · intro resolved
        cases resolved with
        | throughBlocked _ inner => exact (ih entry).mpr inner

/-- Extent checking is deliberately after lexical lookup. -/
theorem nearest (tail : IteratorNames bounds) (name : String) (bound : Nat) :
    (cons (bound := bound) name tail).lookup name = some ⟨bound, .here⟩ := by
  simp [lookup]

theorem outer (tail : IteratorNames bounds) (head name : String) (bound : Nat)
    (different : name ≠ head) :
    (cons (bound := bound) head tail).lookup name =
      (tail.lookup name).map (fun ⟨extent, ref⟩ => ⟨extent, .there ref⟩) := by
  simp only [lookup, if_neg different]

/-- Resolve the lexical binding first, then check its exact axis extent. -/
def lookupAt (names : IteratorNames bounds) (name : String) (extent : Nat) :
    Option (IteratorRef bounds extent) :=
  match names.lookup name with
  | none => none
  | some ⟨bound, ref⟩ => if same : bound = extent then some (same ▸ ref) else none

theorem lookupAt_iff (names : IteratorNames bounds) (name : String) (extent : Nat)
    (ref : IteratorRef bounds extent) :
    names.lookupAt name extent = some ref ↔ Resolves names name ⟨extent, ref⟩ := by
  cases found : names.lookup name with
  | none =>
    simp only [lookupAt, found]
    constructor
    · intro impossible; cases impossible
    · intro resolved
      have success := (lookup_iff names name ⟨extent, ref⟩).mpr resolved
      rw [found] at success
      contradiction
  | some entry =>
    obtain ⟨bound, actual⟩ := entry
    by_cases same : bound = extent
    · subst bound
      simp only [lookupAt, found]
      constructor
      · intro equal
        cases Option.some.inj equal
        exact (lookup_iff names name ⟨extent, ref⟩).mp found
      · intro resolved
        have success := (lookup_iff names name ⟨extent, ref⟩).mpr resolved
        have pairEqual := Option.some.inj (found.symm.trans success)
        cases pairEqual
        rfl
    · simp only [lookupAt, found, dif_neg same]
      constructor
      · intro impossible; cases impossible
      · intro resolved
        have success := (lookup_iff names name ⟨extent, ref⟩).mpr resolved
        have pairEqual := Option.some.inj (found.symm.trans success)
        exact False.elim (same (congrArg Sigma.fst pairEqual))

/-- A wrong-shaped nearer binding is not bypassed to capture an outer one. -/
theorem nearest_mismatch (tail : IteratorNames bounds) (name : String)
    (bound extent : Nat) (different : bound ≠ extent) :
    (cons (bound := bound) name tail).lookupAt name extent = none := by
  simp only [lookupAt, nearest, dif_neg different]

/-- A non-iterator source binding hides every same-named outer iterator,
regardless of its extent. No intrinsic iterator slot is allocated for it. -/
theorem blocked_hides (tail : IteratorNames bounds) (name : String) (extent : Nat) :
    (blocked name tail).lookupAt name extent = none := by
  simp [lookupAt, lookup]

end IteratorNames
end Rumoca.GALEC.Elaboration
