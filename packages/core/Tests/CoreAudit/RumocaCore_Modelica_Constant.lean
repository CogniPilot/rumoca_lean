import RumocaCore.Modelica.Constant
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Modelica.Constant.

#audit axioms Rumoca.ConstantProfile.states_ok
#audit axioms Rumoca.ConstantProfile.rates_ok
#audit axioms Rumoca.ConstantProfile.select
#audit axioms Rumoca.ConstantProfile.select_printed
#audit axioms Rumoca.ConstantProfile.selection
#audit axioms Rumoca.ConstantProfile.parse_eq_parsed
#audit axioms Rumoca.ConstantProfile.Parsed.parseLocated_eq
#audit axioms Rumoca.ConstantProfile.LocatedParsed.resolve
#audit axioms Rumoca.ConstantProfile.LocatedParsed.resolve_complete
#audit axioms Rumoca.ConstantProfile.rateTokens
#audit axioms Rumoca.ConstantProfile.rateExpr
#audit axioms Rumoca.ConstantProfile.rate
#audit axioms Rumoca.ConstantProfile.rate_ok
#audit axioms Rumoca.ConstantProfile.rateExpr_printed
