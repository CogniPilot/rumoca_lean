import Init.Data.Nat.ToString
import RumocaC.Identifier
import Mathlib.Tactic.IntervalCases

/-! Independent base-10 value relation for the decimal constants printed by
the C tree. The proof uses Lean's existing natural-number formatting lemmas. -/
namespace Rumoca.CDecimal

def value (chars : List Char) : Nat :=
  chars.foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0

/-- C treats a leading zero as octal. The decimal printer uses a single zero
or a nonzero leading digit, never a padded digit sequence. -/
def Canonical (chars : List Char) : Prop :=
  chars = ['0'] ∨ ∃ first rest, chars = first :: rest ∧ first ≠ '0'

def Denotes (chars : List Char) (n : Nat) : Prop :=
  Canonical chars ∧ chars.all Char.isDigit = true ∧ value chars = n

private theorem digit_value (n : Nat) (bound : n < 10) :
    n.digitChar.toNat - 48 = n := by
  interval_cases n <;> rfl

private theorem digit_nonzero (n : Nat) (positive : 0 < n) (bound : n < 10) :
    n.digitChar ≠ '0' := by
  interval_cases n <;> first | omega | decide +kernel

private theorem digits_nonzero (n : Nat) (positive : 0 < n) :
    ∃ first rest, Nat.toDigits 10 n = first :: rest ∧ first ≠ '0' := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [Nat.toDigits_eq_if (by decide +kernel)]
      split
      · rename_i small
        exact ⟨n.digitChar, [], rfl, digit_nonzero n positive small⟩
      · rename_i large
        obtain ⟨first, rest, digits, nonzero⟩ := ih (n / 10) (by omega) (by omega)
        exact ⟨first, rest ++ [(n % 10).digitChar], by simp [digits], nonzero⟩

private theorem value_append (chars : List Char) (c : Char) :
    value (chars ++ [c]) = 10 * value chars + (c.toNat - 48) := by
  simp [value, List.foldl_append]

theorem digits_value (n : Nat) : value (Nat.toDigits 10 n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [Nat.toDigits_eq_if (by decide +kernel)]
      split
      · rename_i small
        simp [value, digit_value n small]
      · rename_i large
        rw [value_append, ih (n / 10) (by omega), digit_value (n % 10) (by omega)]
        omega

theorem render_denotes (n : Nat) : Denotes (toString n).toList n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  refine ⟨?_, ?_, digits_value n⟩
  · by_cases zero : n = 0
    · exact Or.inl (by simp [zero])
    · exact Or.inr (digits_nonzero n (by omega))
  · apply List.all_eq_true.mpr
    intro c member
    exact Nat.isDigit_of_mem_toDigits (by decide +kernel) (by decide +kernel) member

theorem denotes_unique (first : Denotes chars a) (second : Denotes chars b) : a = b :=
  first.2.2.symm.trans second.2.2

end Rumoca.CDecimal
