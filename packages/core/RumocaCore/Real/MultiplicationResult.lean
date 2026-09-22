import RumocaCore.Real.AdditionResult

/-! Total nearest/even multiplication of finite binary64 operands. The
independent relation includes signed infinities at the overflow thresholds and
retains the existing signed-zero/gradual-underflow specification on the finite
branch. This models numerical results, not exception flags, traps or the host. -/
noncomputable section
namespace Rumoca.Binary64
open Rumoca.Float64
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

theorem product_below_overflow (a b : Value) :
    value a * value b < overflowValue ↔ units a * units b < overflowUnits * oneUnits := by
  have positive := oneUnits_real_pos
  have cancel : ((overflowUnits : ℝ) / oneUnits) * (oneUnits * oneUnits) =
      (overflowUnits : ℝ) * oneUnits := by
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt positive)]
  unfold value overflowValue
  rw [div_mul_div_comm, div_lt_iff₀ (mul_pos positive positive), cancel]
  exact_mod_cast Iff.rfl

theorem product_above_negative_overflow (a b : Value) :
    -overflowValue < value a * value b ↔ -overflowUnits * oneUnits < units a * units b := by
  have positive := oneUnits_real_pos
  have cancel : (-(overflowUnits : ℝ) / oneUnits) * (oneUnits * oneUnits) =
      -(overflowUnits : ℝ) * oneUnits := by
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt positive)]
  unfold value overflowValue
  rw [← neg_div, div_mul_div_comm, lt_div_iff₀ (mul_pos positive positive), cancel]
  exact_mod_cast Iff.rfl

/-- Mathematical overflow thresholds and the existing independent finite
rounding relation; no implementation equality substitutes for the specification. -/
def MultipliesResult (a b : Value) : Number → Prop
  | .negativeInfinity => value a * value b ≤ -overflowValue
  | .positiveInfinity => overflowValue ≤ value a * value b
  | .finite result => Multiplies a b result
  | .nan => False

def mulResult (a b : Value) : Number :=
  if units a * units b ≤ -overflowUnits * oneUnits then .negativeInfinity
  else if overflowUnits * oneUnits ≤ units a * units b then .positiveInfinity
  else .finite (roundedMul a b)

theorem mulResult_spec (a b : Value) : MultipliesResult a b (mulResult a b) := by
  unfold mulResult
  split
  · change value a * value b ≤ -overflowValue
    exact le_of_not_gt (fun h => not_lt_of_ge ‹_› ((product_above_negative_overflow a b).1 h))
  · split
    · change overflowValue ≤ value a * value b
      exact le_of_not_gt (fun h => not_lt_of_ge ‹_› ((product_below_overflow a b).1 h))
    · exact ⟨⟨lt_of_not_ge ‹_›, lt_of_not_ge ‹_›⟩, roundedMul_spec a b⟩

theorem multipliesResult_unique (first : MultipliesResult a b x)
    (second : MultipliesResult a b y) : x = y := by
  have positive := overflowValue_pos
  cases x <;> cases y <;> simp only [MultipliesResult] at first second
  all_goals try rfl
  case finite.finite x y => exact congrArg Number.finite (product_rounding_unique first.2 second.2)
  all_goals
    try have bounds := (finiteProduct_real a b).1 first.1
    try have bounds := (finiteProduct_real a b).1 second.1
    simp only [overflowValue, neg_div] at *
    exfalso
    linarith

theorem mulResult_correct (a b : Value) (result : Number) :
    mulResult a b = result ↔ MultipliesResult a b result :=
  ⟨fun same => same ▸ mulResult_spec a b,
    fun spec => multipliesResult_unique (mulResult_spec a b) spec⟩

theorem mulResult_finite (a b : Value) (bounded : finiteProduct a b) :
    mulResult a b = .finite (roundedMul a b) := by
  simp only [mulResult, if_neg (not_le_of_gt bounded.1), if_neg (not_le_of_gt bounded.2)]

/-- Exact conservativity of successful finite execution, including signed zero. -/
theorem mulResult_finite_iff (a b result : Value) :
    mulResult a b = .finite result ↔ multiply? a b = some result := by
  rw [mulResult_correct, multiply_correct]
  rfl

theorem mulResult_no_nan (a b : Value) : mulResult a b ≠ .nan := by
  intro same
  exact (mulResult_correct a b .nan).1 same

theorem mulResult_square_not_negative_infinity (a : Value) :
    mulResult a a ≠ .negativeInfinity := by
  intro same
  have negative := (mulResult_correct a a .negativeInfinity).1 same
  change value a * value a ≤ -overflowValue at negative
  have square := mul_self_nonneg (value a)
  have positive := overflowValue_pos
  linarith

end Rumoca.Binary64
