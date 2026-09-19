import RumocaCore.Real.Binary64
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Real.Binary64.

#audit axioms Rumoca.Binary64.round_spec
#audit axioms Rumoca.Binary64.rounding_unique
#audit axioms Rumoca.Binary64.advance_no_overflow
#audit axioms Rumoca.Binary64.advance_exact
#audit axioms Rumoca.Binary64.advance_half_spacing
#audit axioms Rumoca.Binary64.run_error
#audit axioms Rumoca.Binary64.advance_half
#audit axioms Rumoca.Binary64.round_zero
#audit axioms Rumoca.Binary64.roundedAdd_negative_zero
#audit axioms Rumoca.Binary64.roundedAdd_positive_zero
#audit axioms Rumoca.Binary64.run_exact
