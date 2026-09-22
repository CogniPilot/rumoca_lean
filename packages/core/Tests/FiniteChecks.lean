import ProofAudit.Audit
import RumocaCore.Real.Multiplication
import RumocaCore.Real.MultiplicationResult
import RumocaCore.Real.Addition
import RumocaCore.Real.Subtraction
import RumocaCore.Real.Division
import RumocaCore.Solve.Tensor.Finite

/-! General arithmetic contracts, isolated from the unrelated lifecycle and
compiler audit roots so Lake can check this numerical increment independently. -/
#audit axioms Rumoca.Binary64.Scaled.round_spec
#audit axioms Rumoca.Binary64.Scaled.rounding_unique
#audit axioms Rumoca.Binary64.Scaled.round_one
#audit axioms Rumoca.Binary64.Scaled.rounded_zero
#audit axioms Rumoca.Binary64.Scaled.round_underflow
#audit axioms Rumoca.Binary64.Scaled.round_nearest
#audit axioms Rumoca.Binary64.roundedMul_spec
#audit axioms Rumoca.Binary64.product_rounding_unique
#audit axioms Rumoca.Binary64.multiply_correct
#audit axioms Rumoca.Binary64.product_below_overflow
#audit axioms Rumoca.Binary64.product_above_negative_overflow
#audit axioms Rumoca.Binary64.mulResult_spec
#audit axioms Rumoca.Binary64.multipliesResult_unique
#audit axioms Rumoca.Binary64.mulResult_correct
#audit axioms Rumoca.Binary64.mulResult_finite
#audit axioms Rumoca.Binary64.mulResult_finite_iff
#audit axioms Rumoca.Binary64.mulResult_no_nan
#audit axioms Rumoca.Binary64.mulResult_square_not_negative_infinity
#audit axioms Rumoca.Binary64.multiply_complete
#audit axioms Rumoca.Binary64.finiteProduct_real
#audit axioms Rumoca.Binary64.multiply_zero
#audit axioms Rumoca.Binary64.multiply_underflow
#audit axioms Rumoca.Binary64.roundedMul_nearest
#audit axioms Rumoca.Binary64.roundedMul_exact
#audit axioms Rumoca.Binary64.roundedMul_half_spacing
#audit axioms Rumoca.Binary64.roundedAdd_nearest
#audit axioms Rumoca.Binary64.roundedSub_spec
#audit axioms Rumoca.Binary64.difference_rounding_unique
#audit axioms Rumoca.Binary64.roundedSub_nearest
#audit axioms Rumoca.Binary64.roundedSub_eq_add_negate
#audit axioms Rumoca.Binary64.roundedSub_negative_zero
#audit axioms Rumoca.Binary64.subResult_spec
#audit axioms Rumoca.Binary64.subtracts_unique
#audit axioms Rumoca.Binary64.subResult_correct
#audit axioms Rumoca.Binary64.subResult_finite
#audit axioms Rumoca.Binary64.subResult_no_nan
#audit axioms Rumoca.Binary64.subResult_eq_addResult_negate
#audit axioms Rumoca.Binary64.negate_negate
#audit axioms Rumoca.Binary64.roundedDiv_spec
#audit axioms Rumoca.Binary64.quotient_rounding_unique
#audit axioms Rumoca.Binary64.divide_correct
#audit axioms Rumoca.Binary64.divide_complete
#audit axioms Rumoca.Binary64.roundedDiv_nearest
#audit axioms Rumoca.Binary64.roundedDiv_exact
#audit axioms Rumoca.Binary64.roundedDiv_half_spacing
#audit axioms Rumoca.Binary64.roundedDiv_zero
#audit axioms Rumoca.Binary64.finiteQuotient_real
#audit axioms Rumoca.Solve.Tensor.Finite.result_iff
#audit axioms Rumoca.Solve.Tensor.Finite.pointwise_iff
#audit axioms Rumoca.Solve.Tensor.Finite.executes_iff
#audit axioms Rumoca.Solve.Tensor.Finite.execution_complete
#audit axioms Rumoca.Solve.Tensor.Finite.execution_unique
