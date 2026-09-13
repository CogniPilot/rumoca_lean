import RumocaC.StringMemory
import Mathlib.Data.List.TakeWhile

/-! Value specifications for the selected C string library calls (C11
7.24.4.2, 7.24.5.6 and 7.24.6.3). Reuses Lean list prefix and unsigned-byte
comparison. A strcmp result is constrained by sign, not fixed to -1/0/1.
These value specifications do not certify any native library implementation. -/
namespace Rumoca.CStringOperations

def span (bytes accepted : List UInt8) : Nat :=
  (bytes.takeWhile fun byte => accepted.contains byte).length

theorem span_le_length (bytes accepted : List UInt8) : span bytes accepted ≤ bytes.length := by
  exact (List.takeWhile_sublist _).length_le

theorem span_eq_length (bytes accepted : List UInt8) :
    span bytes accepted = bytes.length ↔ ∀ byte ∈ bytes, byte ∈ accepted := by
  have complete : span bytes accepted = bytes.length ↔
      (bytes.takeWhile fun byte => accepted.contains byte) = bytes :=
    ⟨fun same => (List.takeWhile_sublist _).eq_of_length same, congrArg List.length⟩
  rw [complete, List.takeWhile_eq_self_iff]
  simp

def Comparison (left right : List UInt8) (result : Int) : Prop :=
  compare result 0 = compare left right

theorem comparison_zero (compared : Comparison left right result) : result = 0 ↔ left = right := by
  unfold Comparison at compared
  constructor
  · intro zero
    subst result
    have same : compare left right = .eq := compared.symm
    exact Std.LawfulEqOrd.eq_of_compare same
  · intro same
    subst right
    have zero : compare result 0 = .eq := by simpa using compared
    exact Std.LawfulEqOrd.eq_of_compare zero

/-- At least one representable result exists for each comparison. The external
contract also admits every other representable integer with the same sign. -/
theorem comparison_exists (left right : List UInt8) :
    ∃ result : Int, (-(2^31) ≤ result ∧ result < 2^31) ∧ Comparison left right result := by
  cases order : compare left right with
  | lt => exact ⟨-1, by decide, by rw [Comparison, order]; decide⟩
  | eq => exact ⟨0, by decide, by simp [Comparison, order]⟩
  | gt => exact ⟨1, by decide, by rw [Comparison, order]; decide⟩

end Rumoca.CStringOperations
