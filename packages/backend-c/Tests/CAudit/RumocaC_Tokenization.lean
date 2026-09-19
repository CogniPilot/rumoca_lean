import RumocaC.Tokenization
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.Tokenization.

#audit axioms Rumoca.CTokens.Normal.CommentStart.head
#audit axioms Rumoca.CTokens.word_no_comment
#audit axioms Rumoca.CTokens.number_no_comment
#audit axioms Rumoca.CTokens.string_no_comment
#audit axioms Rumoca.CTokens.punctuator_no_comment
#audit axioms Rumoca.CTokens.Consumes.normal
#audit axioms Rumoca.CTokens.Prefix.normal
#audit axioms Rumoca.CTokens.Lexes.normal
