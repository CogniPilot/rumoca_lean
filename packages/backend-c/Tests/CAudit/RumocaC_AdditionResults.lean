import RumocaC.AdditionResults
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.AdditionResults.

#audit axioms Rumoca.CArithmetic.add_result
#audit axioms Rumoca.CArithmetic.add_correct
#audit axioms Rumoca.CArithmetic.add_positive_overflow
#audit axioms Rumoca.CArithmetic.add_negative_overflow
#audit axioms Rumoca.CArithmetic.overflow_not_finite
#audit axioms Rumoca.CArithmetic.positive_overflow_above
#audit axioms Rumoca.CArithmetic.negative_overflow_below
#audit axioms Rumoca.CArithmetic.eval_member_add
#audit axioms Rumoca.CArithmetic.eval_register_add
