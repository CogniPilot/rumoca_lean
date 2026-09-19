import RumocaC.TokenConcatenation
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TokenConcatenation.

#audit axioms Rumoca.CTokens.PhaseSix.Separated.no_rewrite
#audit axioms Rumoca.CTokens.PhaseSix.Separated.unchanged
#audit axioms Rumoca.CTokens.PhaseSix.Separated.empty
#audit axioms Rumoca.CTokens.PhaseSix.Separated.single
#audit axioms Rumoca.CTokens.PhaseSix.Separated.prepend
#audit axioms Rumoca.CTokens.PhaseSix.Separated.append_separator
#audit axioms Rumoca.CTokens.PhaseSix.Separated.all_nonstring
#audit axioms Rumoca.CTokens.PhaseSix.Closed.separated
#audit axioms Rumoca.CTokens.PhaseSix.Closed.empty
#audit axioms Rumoca.CTokens.PhaseSix.Closed.append
#audit axioms Rumoca.CTokens.PhaseSix.Closed.prepend
#audit axioms Rumoca.CTokens.PhaseSix.Closed.seal
#audit axioms Rumoca.CTokens.PhaseSix.Closed.between
#audit axioms Rumoca.CTokens.PhaseSix.Closed.all_nonstring
