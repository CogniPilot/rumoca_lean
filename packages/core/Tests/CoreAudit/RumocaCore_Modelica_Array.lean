import RumocaCore.Modelica.Array
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Modelica.Array.

#audit axioms Rumoca.ArrayProfile.Call.jacobian_iff
#audit axioms Rumoca.ArrayProfile.vector_ok
#audit axioms Rumoca.ArrayProfile.matrix_ok
#audit axioms Rumoca.ArrayProfile.eachArgument_ok
#audit axioms Rumoca.ArrayProfile.trueValue_ok
#audit axioms Rumoca.ArrayProfile.initialization_ok
#audit axioms Rumoca.ArrayProfile.selectProduct_ok
#audit axioms Rumoca.ArrayProfile.selectCall_ok
#audit axioms Rumoca.ArrayProfile.select
#audit axioms Rumoca.ArrayProfile.select_printed
#audit axioms Rumoca.ArrayProfile.selection
#audit axioms Rumoca.ArrayProfile.parse_eq_parsed
#audit axioms Rumoca.ArrayProfile.Parsed.parseLocated_eq
#audit axioms Rumoca.ArrayProfile.LocatedCall.arguments_contained
#audit axioms Rumoca.ArrayProfile.LocatedParsed.callLocation
#audit axioms Rumoca.ArrayProfile.LocatedParsed.resolve
#audit axioms Rumoca.ArrayProfile.LocatedParsed.resolve_complete
#audit axioms Rumoca.ArrayProfile.Model.names
#audit axioms Rumoca.ArrayProfile.Model.Admissible
#audit axioms Rumoca.ArrayProfile.sourceFamily.syntactic
#audit axioms Rumoca.ArrayProfile.select_complete
#audit axioms Rumoca.ArrayProfile.parse_complete
