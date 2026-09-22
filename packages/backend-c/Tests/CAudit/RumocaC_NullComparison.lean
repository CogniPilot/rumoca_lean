import RumocaC.NullComparison
import ProofAudit.Audit

#audit axioms Rumoca.CNull.and_unequal_null_eval
#audit axioms Rumoca.CNull.or_unequal_null_eval
#audit axioms Rumoca.CNull.and_unequal_null_short_circuit

-- Axiom audit for the roots defined in RumocaC.NullComparison.

#audit axioms Rumoca.CNull.Compared.iff
#audit axioms Rumoca.CNull.comparison_iff
#audit axioms Rumoca.CNull.equal_right
#audit axioms Rumoca.CNull.unequal_right
#audit axioms Rumoca.CNull.equal_left
#audit axioms Rumoca.CNull.unequal_left
#audit axioms Rumoca.CNull.nonnull_unsupported
#audit axioms Rumoca.CNull.literal_eval
#audit axioms Rumoca.CNull.zero_variable_not_constant
#audit axioms Rumoca.CNull.equal_eval
#audit axioms Rumoca.CNull.unequal_truth
#audit axioms Rumoca.CNull.branch_preserved
