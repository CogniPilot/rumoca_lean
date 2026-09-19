import RumocaC.TokenStarts
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TokenStarts.

#audit axioms Rumoca.CTokens.Competition.Starts.append
#audit axioms Rumoca.CTokens.Competition.Starts.prefix
#audit axioms Rumoca.CTokens.Competition.Starts.head
#audit axioms Rumoca.CTokens.Competition.nondigit_starts
#audit axioms Rumoca.CTokens.Competition.identifier_starts
#audit axioms Rumoca.CTokens.Competition.IdentifierStart.not_digit
#audit axioms Rumoca.CTokens.Competition.NumberStart.append
#audit axioms Rumoca.CTokens.Competition.NumberStart.prefix
#audit axioms Rumoca.CTokens.Competition.number_starts
#audit axioms Rumoca.CTokens.Competition.identifier_no_quote
#audit axioms Rumoca.CTokens.Competition.word_not_encoded
#audit axioms Rumoca.CTokens.Competition.NumberStart.not_identifier
#audit axioms Rumoca.CTokens.Competition.word_not_number
#audit axioms Rumoca.CTokens.Competition.Starts.disjoint
#audit axioms Rumoca.CTokens.Competition.Starts.positive
#audit axioms Rumoca.CTokens.Competition.IdentifierStart.character
#audit axioms Rumoca.CTokens.Competition.NumberStart.first
#audit axioms Rumoca.CTokens.Competition.encoded_starts
#audit axioms Rumoca.CTokens.Competition.word_starts
#audit axioms Rumoca.CTokens.Competition.number_start_not_identifier
#audit axioms Rumoca.CTokens.Competition.number_input_starts
#audit axioms Rumoca.CTokens.Competition.quoted_starts
#audit axioms Rumoca.CTokens.Competition.string_input_starts
