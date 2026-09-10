import ProofAudit.Audit
import RumocaCore.Real.Multiplication
import RumocaCore.Real.Addition
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
#audit axioms Rumoca.Binary64.multiply_complete
#audit axioms Rumoca.Binary64.finiteProduct_real
#audit axioms Rumoca.Binary64.multiply_zero
#audit axioms Rumoca.Binary64.multiply_underflow
#audit axioms Rumoca.Binary64.roundedMul_nearest
#audit axioms Rumoca.Binary64.roundedMul_exact
#audit axioms Rumoca.Binary64.roundedMul_half_spacing
#audit axioms Rumoca.Binary64.roundedAdd_nearest
#audit axioms Rumoca.Solve.Tensor.Finite.result_iff
#audit axioms Rumoca.Solve.Tensor.Finite.pointwise_iff
#audit axioms Rumoca.Solve.Tensor.Finite.executes_iff
#audit axioms Rumoca.Solve.Tensor.Finite.execution_complete
#audit axioms Rumoca.Solve.Tensor.Finite.execution_unique
