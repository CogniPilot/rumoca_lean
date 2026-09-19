import RumocaC.TreeConcatenation
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.TreeConcatenation.

#audit axioms Rumoca.CTree.Syntax.TypeTokens.nonstring
#audit axioms Rumoca.CTree.Syntax.Expression.separated
#audit axioms Rumoca.CTree.Syntax.BlockItem.closed
#audit axioms Rumoca.CTree.Syntax.BlockItems.closed
#audit axioms Rumoca.CTree.Syntax.ParameterPhrase.nonstring
#audit axioms Rumoca.CTree.Syntax.ParametersPhrase.nonstring
#audit axioms Rumoca.CTree.Syntax.SignaturePhrase.nonstring
#audit axioms Rumoca.CTree.Syntax.FunctionPhrase.closed
#audit axioms Rumoca.CTree.Syntax.FunctionPhrase.concatenation_unchanged
#audit axioms Rumoca.CTree.Printer.FunctionDenotes.phase_six
