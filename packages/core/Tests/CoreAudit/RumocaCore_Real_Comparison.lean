import RumocaCore.Real.Comparison
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Real.Comparison.

#audit axioms Rumoca.Float64.decode_finite
#audit axioms Rumoca.Float64.decode_nan
#audit axioms Rumoca.Float64.value_eq_iff
#audit axioms Rumoca.Float64.value_lt_iff
#audit axioms Rumoca.Float64.value_le_iff
#audit axioms Rumoca.Float64.test_finite
#audit axioms Rumoca.Float64.test_finite_false
#audit axioms Rumoca.Float64.unordered_left
#audit axioms Rumoca.Float64.unordered_right
