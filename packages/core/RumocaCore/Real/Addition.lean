import RumocaCore.Real.ScaledRounding

/-! Real refinement of the existing ordered binary64 addition primitive.
Its finite overflow guard is a separate execution-domain obligation. -/
namespace Rumoca.Binary64

theorem roundedAdd_nearest (a b candidate : Value) :
    |value (roundedAdd a b) - (value a + value b)| ≤ |value candidate - (value a + value b)| := by
  by_cases hz : a = negativeZero ∧ b = negativeZero
  · obtain ⟨rfl, rfl⟩ := hz
    have hu : units negativeZero = 0 := by decide +kernel
    have hv : value negativeZero = 0 := by simp only [value, hu, Int.cast_zero, zero_div]
    rw [roundedAdd_negative_zero, hv, add_zero, sub_zero, abs_zero]
    exact abs_nonneg _
  · have h := Scaled.round_nearest 1 (by decide) (units a + units b) candidate
    have he : ((units a + units b : Int) : ℝ) / ((1 : Nat) * oneUnits) = value a + value b := by
      simp only [Int.cast_add, Nat.cast_one, one_mul, add_div, value]
    rw [Scaled.round_one, he] at h
    simpa only [roundedAdd, if_neg hz] using h

end Rumoca.Binary64
