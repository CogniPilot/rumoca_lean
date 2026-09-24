import Parser.DecimalNat

/-! Canonical unsigned decimal numerals for static Integer positions (extents,
bounds and axes). The pinned eFMI integer rule has no leading zeros, so a
numeral is admitted exactly when it is the canonical rendering of its value;
`Parser.DecimalNat` alone would also accept spellings such as `01`. -/
namespace Rumoca.GALEC.Elaboration.Static.Numeral
open _root_.Parser

def read (spelling : String) : Option Nat :=
  (DecimalNat.parse spelling).bind fun value =>
    if toString value = spelling then some value else none

/-- Admission is exactly canonical rendering. -/
theorem read_iff (spelling : String) (value : Nat) :
    read spelling = some value ↔ spelling = toString value := by
  constructor
  · intro found
    obtain ⟨candidate, _, canonical⟩ := Option.bind_eq_some_iff.mp found
    split at canonical
    · rename_i same
      cases Option.some.inj canonical
      exact same.symm
    · contradiction
  · rintro rfl
    simp only [read, DecimalNat.parse_render, Option.bind_some, if_true]

theorem canonical_denotes (canonical : spelling = toString value) :
    DecimalNat.Denotes spelling value := by
  subst canonical
  exact DecimalNat.render_denotes value

end Rumoca.GALEC.Elaboration.Static.Numeral
