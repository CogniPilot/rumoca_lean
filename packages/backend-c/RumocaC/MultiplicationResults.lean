import RumocaC.Loops

/-! Exact finite-input multiplication outcomes in the canonical C arithmetic
rule. No overflow guard is needed; nonfinite operands remain outside this rule. -/
noncomputable section
namespace Rumoca.CArithmetic
open CMemory CTree Binary64
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

theorem mul_result (a b : Binary64.Value) :
    floatMul (.finite a) (.finite b) = some (.float64 (mulResult a b).encode) := by
  simp only [floatMul, CCalls.finiteValue_finite, bind, Option.bind_some, pure]

theorem mul_correct (a b : Binary64.Value) (result : CMemory.Value) :
    floatMul (.finite a) (.finite b) = some result ↔
      ∃ number, Binary64.MultipliesResult a b number ∧ result = .float64 number.encode := by
  rw [mul_result, Option.some.injEq]
  constructor
  · intro same
    exact ⟨mulResult a b, mulResult_spec a b, same.symm⟩
  · rintro ⟨number, spec, rfl⟩
    rw [(mulResult_correct a b number).2 spec]

theorem mul_positive_overflow (a b : Binary64.Value)
    (large : overflowValue ≤ value a * value b) :
    floatMul (.finite a) (.finite b) = some (.float64 Float64.Number.positiveInfinity.encode) := by
  rw [mul_result, (mulResult_correct a b .positiveInfinity).2 large]

theorem mul_negative_overflow (a b : Binary64.Value)
    (small : value a * value b ≤ -overflowValue) :
    floatMul (.finite a) (.finite b) = some (.float64 Float64.Number.negativeInfinity.encode) := by
  rw [mul_result, (mulResult_correct a b .negativeInfinity).2 small]

theorem eval_mul (expressions : CBody.Expressions) (env : CBody.Locals)
    (types : CLoops.Types) (heap : Heap) (left right : Expr) (a b : Binary64.Value)
    (leftValue : expressions.value env heap left = some (.finite a))
    (rightValue : expressions.value env heap right = some (.finite b)) :
    CLoops.evalWith expressions env types heap (.bin .mul left right) =
      some (.float64 (mulResult a b).encode) := by
  simp only [CLoops.evalWith, leftValue, rightValue, bind, Option.bind_some, mul_result]

end Rumoca.CArithmetic
