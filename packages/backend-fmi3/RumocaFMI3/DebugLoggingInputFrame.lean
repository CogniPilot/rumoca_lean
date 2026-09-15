import RumocaFMI3.DebugLoggingLoop
import RumocaC.StringMemoryFrame

/-! Original category arrays and strings survive any call that frames their
read cells. Null entries need no character region, and an empty array needs no
region at all. This supports caller resources across mixed runtime histories. -/
namespace Rumoca.FMI3.DebugLogging
open CMemory CStringMemory

def InputRegion (pointer : Option Address) (n : Nat) (selected : Nat → Option Address)
    (bytes : Nat → List UInt8) (q : Address) : Prop :=
  ∃ base i, pointer = some base ∧ i < n ∧
    (q = base.index i ∨ ∃ text, selected i = some text ∧
      ∃ j ≤ (bytes i).length, q = text.index j)

theorem input_empty : ¬ InputRegion pointer 0 selected bytes q := by
  rintro ⟨_, _, _, impossible, _⟩
  exact Nat.not_lt_zero _ impossible

theorem Entries.load_ne_none (entries : Entries heap pointer n selected bytes)
    (inside : InputRegion pointer n selected bytes q) : load heap q ≠ none := by
  obtain ⟨base, i, same, bound, cell⟩ := inside
  obtain ⟨actual, named, loaded, strings⟩ := entries i bound
  have equal : actual = base := Option.some.inj (named.symm.trans same)
  subst actual
  rcases cell with rfl | ⟨text, chosen, j, valid, rfl⟩
  · simp [loaded]
  · exact (strings text chosen).load_ne_none valid

theorem Entries.framed (entries : Entries before pointer n selected bytes)
    (frame : ∀ q, InputRegion pointer n selected bytes q → after q = before q) :
    Entries after pointer n selected bytes := by
  intro i inside
  obtain ⟨base, same, loaded, strings⟩ := entries i inside
  refine ⟨base, same, ?_, ?_⟩
  · simpa only [load, frame (base.index i) ⟨base, i, same, inside, Or.inl rfl⟩] using loaded
  · intro text chosen
    apply (strings text chosen).framed
    intro j bound
    exact frame _ ⟨base, i, same, inside, Or.inr ⟨text, chosen, j, bound, rfl⟩⟩

end Rumoca.FMI3.DebugLogging
