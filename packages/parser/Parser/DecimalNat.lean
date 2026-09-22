import Init.Data.Nat.ToString
import Mathlib.Tactic.IntervalCases

/-! Unsigned mathematical base-ten numerals. This generic helper owns neither
frontend Token categories nor source/target Integer admission policy. It permits
leading zeros as decimal, not C octal. Character validation is exactly ASCII
`Char.isDigit` (the inclusive '0'..'9' interval), with no signs or separators. -/
namespace Parser.DecimalNat

/-- Mathematical left-to-right base-ten accumulation. For arbitrary characters
this function is total; only `Denotes`/`parse` impose numeral validity. -/
def value (chars : List Char) : Nat :=
  chars.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- Independent numeral meaning: a nonempty ASCII digit string and its exact
mathematical fold value. In particular this definition never invokes `parse`. -/
def Denotes (s : String) (n : Nat) : Prop :=
  s.toList ≠ [] ∧ s.toList.all Char.isDigit = true ∧ value s.toList = n

def parse (s : String) : Option Nat :=
  let chars := s.toList
  if chars ≠ [] ∧ chars.all Char.isDigit = true then some (value chars) else none

theorem parse_iff (s : String) (n : Nat) : parse s = some n ↔ Denotes s n := by
  unfold parse Denotes
  dsimp only
  split <;> simp_all

theorem denotes_unique (first : Denotes s a) (second : Denotes s b) : a = b :=
  first.2.2.symm.trans second.2.2

private theorem digit_value (n : Nat) (bound : n < 10) :
    n.digitChar.toNat - 48 = n := by
  interval_cases n <;> rfl

private theorem value_append (chars : List Char) (c : Char) :
    value (chars ++ [c]) = value chars * 10 + (c.toNat - 48) := by
  simp [value, List.foldl_append]

private theorem digits_value (n : Nat) : value (Nat.toDigits 10 n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · rename_i small
      simp [value, digit_value n small]
    · rename_i large
      rw [value_append, ih (n / 10) (by omega), digit_value (n % 10) (by omega)]
      omega

theorem render_denotes (n : Nat) : Denotes (toString n) n := by
  unfold Denotes
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  refine ⟨?_, ?_, digits_value n⟩
  · have positive := Nat.length_toDigits_pos (b := 10) (n := n)
    intro empty
    simp [empty] at positive
  · apply List.all_eq_true.mpr
    intro c member
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) member

theorem parse_render (n : Nat) : parse (toString n) = some n :=
  (parse_iff (toString n) n).mpr (render_denotes n)

end Parser.DecimalNat
