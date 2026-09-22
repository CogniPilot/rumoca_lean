import RumocaC.Loops

/-! Exact C result encoding and overflow observations for finite addition.
The ordinary typed expression machine consumes this same arithmetic rule. -/
namespace Rumoca.CArithmetic
open CMemory CTree Binary64
noncomputable section
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

theorem add_result (a b : Binary64.Value) :
    floatAdd (.finite a) (.finite b) = some (.float64 (addResult a b).encode) := by
  simp only [floatAdd, CCalls.finiteValue_finite, bind, Option.bind_some, pure]

/-- The target result is characterized by the independent mathematical
addition relation and its encoding, including both overflow outcomes. -/
theorem add_correct (a b : Binary64.Value) (result : CMemory.Value) :
    floatAdd (.finite a) (.finite b) = some result ↔
      ∃ number, Binary64.Adds a b number ∧ result = .float64 number.encode := by
  rw [add_result, Option.some.injEq]
  constructor
  · intro same
    exact ⟨addResult a b, addResult_spec a b, same.symm⟩
  · rintro ⟨number, spec, rfl⟩
    rw [(addResult_correct a b number).mpr spec]

theorem add_positive_overflow (a b : Binary64.Value)
    (large : overflowValue ≤ value a + value b) :
    floatAdd (.finite a) (.finite b) = some (.float64 Float64.Number.positiveInfinity.encode) := by
  rw [add_result, (addResult_correct a b .positiveInfinity).mpr large]

theorem add_negative_overflow (a b : Binary64.Value)
    (small : value a + value b ≤ -overflowValue) :
    floatAdd (.finite a) (.finite b) = some (.float64 Float64.Number.negativeInfinity.encode) := by
  rw [add_result, (addResult_correct a b .negativeInfinity).mpr small]

theorem overflow_not_finite (sign : Bool) :
    (Value.float64 (if sign then Float64.Number.negativeInfinity.encode else
      Float64.Number.positiveInfinity.encode)).isFinite = some false := by
  cases sign <;> decide +kernel

theorem positive_overflow_above (x : Binary64.Value) :
    Float64.test .gt Float64.Number.positiveInfinity.encode (toBits x).val = true := by
  simp [Float64.test, Float64.compareBits, Float64.Number.compare]

theorem negative_overflow_below (x : Binary64.Value) :
    Float64.test .lt Float64.Number.negativeInfinity.encode (toBits x).val = true := by
  simp [Float64.test, Float64.compareBits, Float64.Number.compare]

section
variable [interface : CInterface]

/-- The generic member-read addition used by adapter clock declarations,
with no finite-result premise. Both operands must have finite values. -/
theorem eval_member_add (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (base right : Expr) (member : String) (pointer : Bool) (a b : Binary64.Value)
    (leftValue : CBody.eval env heap (.field base member pointer) = some (.finite a))
    (rightValue : CBody.eval env heap right = some (.finite b)) :
    CLoops.eval env types heap (.bin .add (.field base member pointer) right) =
      some (.float64 (addResult a b).encode) := by
  simp only [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, leftValue, rightValue, bind, Option.bind_some, add_result]

/-- Prepared floating registers use the same addition rule; unsigned size
arithmetic cannot take precedence for a declared floating left operand. -/
theorem eval_register_add (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (left right : String) (a b : Binary64.Value)
    (leftType : types left = some .float64)
    (leftValue : CBody.eval env heap (.id left) = some (.finite a))
    (rightValue : CBody.eval env heap (.id right) = some (.finite b)) :
    CLoops.eval env types heap (.bin .add (.id left) (.id right)) =
      some (.float64 (addResult a b).encode) := by
  simp only [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, leftType, Option.some.injEq, reduceCtorEq, false_and, ↓reduceIte,
    leftValue, rightValue, bind, Option.bind_some, add_result]

end

end
end Rumoca.CArithmetic
