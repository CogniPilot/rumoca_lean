import RumocaCore.Modelica.Selection
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaCore.Modelica.Selection.

#audit axioms Rumoca.Modelica.Selection.selectLocated
#audit axioms Rumoca.Modelica.Selection.Parsed.lexical
#audit axioms Rumoca.Modelica.Selection.Parsed.tokens_eq
#audit axioms Rumoca.Modelica.Selection.Parsed.lexes
#audit axioms Rumoca.Modelica.Selection.Parsed.in_ebnf
#audit axioms Rumoca.Modelica.Selection.parse
#audit axioms Rumoca.Modelica.Selection.parse_eq_parsed
#audit axioms Rumoca.Modelica.Selection.Parsed.unique
#audit axioms Rumoca.Modelica.Selection.LocatedParsed.aligned
#audit axioms Rumoca.Modelica.Selection.LocatedParsed.erases
#audit axioms Rumoca.Modelica.Selection.LocatedParsed.lexemes
#audit axioms Rumoca.Modelica.Selection.LocatedParsed.disjoint
#audit axioms Rumoca.Modelica.Selection.LocatedParsed.tokenSpan_text
#audit axioms Rumoca.Modelica.Selection.LocatedParsed.tokenSpan_record
#audit axioms Rumoca.Modelica.Selection.parseLocated
#audit axioms Rumoca.Modelica.Selection.Parsed.located_parsed
#audit axioms Rumoca.Modelica.Selection.Parsed.parseLocated_eq
#audit axioms Rumoca.Modelica.Selection.parseLocated_complete
#audit axioms Rumoca.Modelica.Selection.Uncommented
#audit axioms Rumoca.Modelica.Selection.Parsed.tokens_lexemes
#audit axioms Rumoca.Modelica.Selection.LocatedParsed.codeLocations_eq
#audit axioms Rumoca.Modelica.Selection.LocatedParsed.tokenSpan_eq
#audit axioms Rumoca.Modelica.Selection.commentSpan
