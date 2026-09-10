import RumocaCore.Real.Binary64

/-! Exact rational-input rounding on the existing finite binary64 grid.
`numerator / scale` is measured in units of 2^-1074. Comparing integer
cross-products preserves all product bits; no intermediate division or
rounding is performed. As with the original rounding specification, finite
minimization is proof-only and is never executed by the compiler. -/
namespace Rumoca.Binary64.Scaled

def distance (scale : Nat) (numerator : Int) (x : Value) : Nat :=
  (units x * scale - numerator).natAbs

private def cost (scale : Nat) (numerator : Int) (x : Value) : Nat :=
  (distance scale numerator x * 2 + parity x) * count + x.val

private theorem minimum_exists (scale : Nat) (numerator : Int) :
    ∃ x : Value, ∀ y : Value, cost scale numerator x ≤ cost scale numerator y := by
  obtain ⟨x, _, hx⟩ := Finset.exists_min_image Finset.univ (cost scale numerator)
    (show (Finset.univ : Finset Value).Nonempty from ⟨one, Finset.mem_univ _⟩)
  exact ⟨x, fun y => hx y (Finset.mem_univ y)⟩

private noncomputable opaque witness (scale : Nat) (numerator : Int) :
    {x : Value // ∀ y : Value, cost scale numerator x ≤ cost scale numerator y} :=
  ⟨Classical.choose (minimum_exists scale numerator),
    Classical.choose_spec (minimum_exists scale numerator)⟩

noncomputable def round (scale : Nat) (numerator : Int) : Value := (witness scale numerator).val

/-- The same nearest/even/canonical rule as integer-input rounding, now
comparing exact rational inputs without discarding their fractional bits.
Signed operation-specific zeros are handled after this canonical rounding. -/
structure RoundsNearestEven (scale : Nat) (numerator : Int) (x : Value) : Prop where
  nearest : ∀ y, distance scale numerator x ≤ distance scale numerator y
  even : ∀ y, distance scale numerator x = distance scale numerator y → parity x ≤ parity y
  canonical : ∀ y, distance scale numerator x = distance scale numerator y →
    parity x = parity y → x.val ≤ y.val

theorem round_spec (scale : Nat) (numerator : Int) : RoundsNearestEven scale numerator (round scale numerator) := by
  have hc := (witness scale numerator).property
  change ∀ y, cost scale numerator (round scale numerator) ≤ cost scale numerator y at hc
  refine ⟨?_, ?_, ?_⟩
  · intro y
    have h := hc y
    have hp := parity_bound (round scale numerator)
    have hq := parity_bound y
    have hr := (round scale numerator).isLt
    have hy := y.isLt
    simp only [cost, count, magnitudeCount, fractionCount] at h hr hy
    omega
  · intro y hd
    have h := hc y
    have hp := parity_bound (round scale numerator)
    have hq := parity_bound y
    have hr := (round scale numerator).isLt
    have hy := y.isLt
    simp only [cost, hd, count, magnitudeCount, fractionCount] at h hr hy
    omega
  · intro y hd hp
    have h := hc y
    simp only [cost, hd, hp] at h
    omega

theorem rounding_unique (ha : RoundsNearestEven scale numerator a)
    (hb : RoundsNearestEven scale numerator b) : a = b := by
  have hd := Nat.le_antisymm (ha.nearest b) (hb.nearest a)
  have hp := Nat.le_antisymm (ha.even b hd) (hb.even a hd.symm)
  exact Fin.ext (Nat.le_antisymm (ha.canonical b hd hp) (hb.canonical a hd.symm hp.symm))

theorem round_one (numerator : Int) : round 1 numerator = Binary64.round numerator := by
  apply Binary64.rounding_unique _ (Binary64.round_spec numerator)
  have h := round_spec 1 numerator
  exact ⟨by simpa only [distance, Nat.cast_one, mul_one, Binary64.distance] using h.nearest,
    by simpa only [distance, Nat.cast_one, mul_one, Binary64.distance] using h.even,
    by simpa only [distance, Nat.cast_one, mul_one, Binary64.distance] using h.canonical⟩

theorem round_zero (scale : Nat) : round scale 0 = positiveZero := by
  have h := (witness scale 0).property positiveZero
  have hz : cost scale 0 positiveZero = 0 := by
    have hu : units positiveZero = 0 := by decide +kernel
    have hp : parity positiveZero = 0 := by decide +kernel
    simp only [cost, distance, hu, hp, zero_mul, sub_zero, Int.natAbs_zero, zero_add]
    rfl
  change cost scale 0 (round scale 0) ≤ cost scale 0 positiveZero at h
  rw [hz] at h
  apply Fin.ext
  unfold cost at h
  change (round scale 0).val = 0
  omega

/-- Any rounded zero is the canonical positive encoding, even when the exact
input is a tiny nonzero rational that underflows. -/
theorem rounded_zero (h : units (round scale numerator) = 0) :
    round scale numerator = positiveZero := by
  have spec := round_spec scale numerator
  have hu : units positiveZero = 0 := by decide +kernel
  have hp : parity positiveZero = 0 := by decide +kernel
  have hd : distance scale numerator (round scale numerator) = distance scale numerator positiveZero := by
    simp only [distance, h, hu]
  have he : parity (round scale numerator) = parity positiveZero := Nat.le_antisymm
    (spec.even positiveZero hd) (by rw [hp]; exact Nat.zero_le _)
  have hc := spec.canonical positiveZero hd he
  apply Fin.ext
  change (round scale numerator).val = 0
  change (round scale numerator).val ≤ 0 at hc
  omega

/-- Every exact input strictly below half the least subnormal rounds to
zero. The operation can then supply the sign; no tiny input is truncated. -/
theorem round_underflow (small : 2 * numerator.natAbs < scale) :
    round scale numerator = positiveZero := by
  apply rounded_zero
  have hz : units positiveZero = 0 := by decide +kernel
  have nearest := (round_spec scale numerator).nearest positiveZero
  simp only [distance, hz, zero_mul, zero_sub, Int.natAbs_neg] at nearest
  have triangle := Int.natAbs_add_le (units (round scale numerator) * scale - numerator) numerator
  rw [sub_add_cancel, Int.natAbs_mul, Int.natAbs_natCast] at triangle
  by_contra nonzero
  have positive := Int.natAbs_pos.mpr nonzero
  have lower := Nat.le_mul_of_pos_left scale positive
  omega

private theorem error_scale (scale : Nat) (positive : 0 < scale) (numerator : Int) (x : Value) :
    |value x - (numerator : ℝ) / (scale * oneUnits)| =
      (distance scale numerator x : ℝ) / (scale * oneUnits) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast positive
  have he : value x - (numerator : ℝ) / (scale * oneUnits) =
      ((units x : ℝ) * scale - numerator) / (scale * oneUnits) := by
    have hx : ((units x : ℝ) * scale) / (scale * oneUnits) = value x := by
      rw [mul_comm (scale : ℝ) (oneUnits : ℝ), mul_div_mul_right _ _ (ne_of_gt hs)]
      rfl
    rw [sub_div, hx]
  rw [he, abs_div, abs_of_pos (mul_pos hs oneUnits_real_pos)]
  congr 1
  simp only [distance, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_natCast]

/-- A Real nearest-value result for every positive denominator, including
inputs between adjacent subnormals. -/
theorem round_nearest (scale : Nat) (positive : 0 < scale) (numerator : Int) (y : Value) :
    |value (round scale numerator) - (numerator : ℝ) / (scale * oneUnits)| ≤
      |value y - (numerator : ℝ) / (scale * oneUnits)| := by
  rw [error_scale scale positive, error_scale scale positive]
  apply (div_le_div_iff_of_pos_right (mul_pos (by exact_mod_cast positive) oneUnits_real_pos)).mpr
  exact_mod_cast (round_spec scale numerator).nearest y

end Rumoca.Binary64.Scaled
