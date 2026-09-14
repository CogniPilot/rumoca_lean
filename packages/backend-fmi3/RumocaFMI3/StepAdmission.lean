import RumocaC.MathCalls
import RumocaC.IntegerConversions
import RumocaC.Statements
import RumocaC.AdditionResults

/-! Derive the bounded solver count from the mathematical content of the
actual CS duration guards. These are admission consequences, not a public
call contract or a claim about unmodeled native floating-point settings. -/
noncomputable section
namespace Rumoca.FMI3.StepAdmission
open CMemory
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

def AdmittedDuration (step : Binary64.Value) : Prop :=
  0 < Binary64.value step ∧ Binary64.value step ≤ 1000000 ∧
    Binary64.value (Binary64.floorValue step) = Binary64.value step

/-- Accepted duration guards supply a positive bounded counter and the
ordinary C cast used by `model_advance`. The cast is derived, not assumed. -/
theorem duration_count (step : Binary64.Value) (accepted : AdmittedDuration step) :
    ∃ count : CStatements.Counter, 0 < count.val ∧ count.val ≤ 1000000 ∧
      Binary64.value step = (count.val : ℝ) ∧
      convert .size (.finite step) = some (.integer count.val) := by
  obtain ⟨positive, bounded, integral⟩ := accepted
  obtain ⟨z, exactValue⟩ := (Binary64.floorValue_fixed_iff step).mp integral
  have zpositive : 0 < z := by exact_mod_cast (exactValue ▸ positive)
  have zbounded : z ≤ 1000000 := by exact_mod_cast (exactValue ▸ bounded)
  have restored : (z.toNat : Int) = z := Int.toNat_of_nonneg zpositive.le
  have small : z.toNat < 2 ^ 64 := by omega
  let count : CStatements.Counter := ⟨z.toNat, small⟩
  have same : Binary64.value step = (count.val : ℝ) := by
    change Binary64.value step = (z.toNat : ℝ)
    rw [← Int.cast_natCast, restored]
    exact exactValue
  refine ⟨count, ?_, ?_, same, ?_⟩
  · change 0 < z.toNat
    omega
  · change z.toNat ≤ 1000000
    omega
  · apply (CIntegerConversions.finite_size_iff step (count.val : Int)).mpr
    refine ⟨(Binary64.truncateInteger_exact step (count.val : Int) ?_).symm, ?_, ?_⟩
    · simpa only [Int.cast_natCast] using same
    · exact Int.natCast_nonneg _
    · exact_mod_cast count.isLt

/-- The invoked count has a unique mathematical duration; representational
choices such as signed zero cannot introduce a second accepted count. -/
theorem count_unique (step : Binary64.Value) (left right : CStatements.Counter)
    (leftDuration : Binary64.value step = (left.val : ℝ))
    (rightDuration : Binary64.value step = (right.val : ℝ)) : left = right := by
  apply Fin.ext
  exact_mod_cast leftDuration.symm.trans rightDuration

theorem duration_of_count (step : Binary64.Value) (count : CStatements.Counter)
    (positive : 0 < count.val) (bounded : count.val ≤ 1000000)
    (duration : Binary64.value step = (count.val : ℝ)) : AdmittedDuration step := by
  refine ⟨?_, ?_, (Binary64.floorValue_fixed_iff step).mpr ⟨count.val, ?_⟩⟩
  · rw [duration]
    exact_mod_cast positive
  · rw [duration]
    exact_mod_cast bounded
  · simpa only [Int.cast_natCast] using duration

/-- Every admitted duration is below the overflow gap, for every finite
starting clock. This cannot justify skipping the actual earlier addition on
rejected inputs; those inputs require the signed-infinity result semantics. -/
theorem duration_sum (time step : Binary64.Value) (accepted : AdmittedDuration step) :
    Binary64.addResult time step = .finite (Binary64.roundedAdd time step) := by
  have positive : 0 < (Binary64.units step : ℝ) := by
    have scaled := (lt_div_iff₀ Binary64.oneUnits_real_pos).mp accepted.1
    simpa only [zero_mul] using scaled
  have bounded : (Binary64.units step : ℝ) ≤ 1000000 * (Binary64.oneUnits : ℝ) :=
    (div_le_iff₀ Binary64.oneUnits_real_pos).mp accepted.2.1
  have integerPositive : 0 < Binary64.units step := by exact_mod_cast positive
  have integerBound : Binary64.units step ≤ 1000000 * (Binary64.oneUnits : Int) := by
    exact_mod_cast bounded
  have gap : 1000000 * (Binary64.oneUnits : Int) < 2 ^ 2044 := by decide +kernel
  have timeBound := Binary64.units_bound time
  apply Binary64.addResult_finite
  unfold Binary64.overflowUnits
  constructor <;> omega

/-- The non-advance guard still has to pass after duration admission. Exact
integer duration does not imply that binary64 communication time advances. -/
theorem duration_progress (time step : Binary64.Value) (accepted : AdmittedDuration step) :
    Float64.test .le (Binary64.addResult time step).encode (Binary64.toBits time).val = false ↔
      Binary64.value time < Binary64.value (Binary64.roundedAdd time step) := by
  rw [duration_sum time step accepted]
  simp only [Float64.Number.encode, Float64.test_finite_false, Float64.Relation.Holds,
    not_le]

variable [interface : CInterface]

/-- Exact C comparison results characterize mathematical duration admission
after the ordinary floor call has supplied its result. This includes signed
zero and uses the encoded integer literals from the actual comparisons. -/
theorem duration_checks (env : CBody.Locals) (heap : Heap) (step : Binary64.Value)
    (stepName floorName : String)
    (stepBound : env stepName = some (.finite step))
    (floorBound : env floorName = some (.finite (Binary64.floorValue step))) :
    (CBody.eval env heap (.bin .le (.id stepName) (.nat 0)) = some (CBody.boolean false) ∧
     CBody.eval env heap (.bin .ne (.id floorName) (.id stepName)) = some (CBody.boolean false) ∧
     CBody.eval env heap (.bin .gt (.id stepName) (.nat 1000000)) = some (CBody.boolean false)) ↔
      AdmittedDuration step := by
  have false_iff (b : Bool) : CBody.boolean b = CBody.boolean false ↔ b = false := by
    cases b <;> decide
  simp only [CBody.eval, CBody.resolve, stepBound, floorBound, Option.orElse_some,
    Option.bind_eq_bind, Option.bind_some, Value.finite, CBody.comparison, Nat.cast_zero, Nat.cast_ofNat]
  rw [CIntegerConversions.integer_float64 0 (by decide +kernel),
    CIntegerConversions.integer_float64 1000000 (by decide +kernel)]
  simp only [Option.bind_some, Value.finite, CBody.floatComparison, Option.some.injEq,
    false_iff, Float64.test_finite_false, Float64.Relation.Holds,
    Binary64.ofSmallInt_value, Int.cast_ofNat, Int.cast_zero, not_le, not_lt, not_not,
    AdmittedDuration]
  exact and_congr_right (fun _ => and_comm)

end Rumoca.FMI3.StepAdmission
end
