import RumocaCore.Real.AdditionResult
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Real.AdditionResult.

#audit axioms Rumoca.Float64.decode_encode
#audit axioms Rumoca.Float64.encode_injective
#audit axioms Rumoca.Binary64.roundedAdd_spec
#audit axioms Rumoca.Binary64.sum_rounding_unique
#audit axioms Rumoca.Binary64.overflowValue_pos
#audit axioms Rumoca.Binary64.sum_below_overflow
#audit axioms Rumoca.Binary64.sum_above_negative_overflow
#audit axioms Rumoca.Binary64.addResult_spec
#audit axioms Rumoca.Binary64.adds_unique
#audit axioms Rumoca.Binary64.addResult_correct
#audit axioms Rumoca.Binary64.addResult_finite
#audit axioms Rumoca.Binary64.addResult_no_nan
