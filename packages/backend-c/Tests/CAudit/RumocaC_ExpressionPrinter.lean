import RumocaC.ExpressionPrinter
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.ExpressionPrinter.

#audit axioms Rumoca.CTree.Printer.tail_safe_separator
#audit axioms Rumoca.CTree.Printer.identifier_renders
#audit axioms Rumoca.CTree.Printer.natural_renders
#audit axioms Rumoca.CTree.Printer.string_renders
#audit axioms Rumoca.CTree.Printer.binary_renders
#audit axioms Rumoca.CTree.Printer.unary_renders
#audit axioms Rumoca.CTree.Printer.cast_renders
#audit axioms Rumoca.CTree.Printer.sizeof_renders
#audit axioms Rumoca.CTree.Printer.index_renders
#audit axioms Rumoca.CTree.Printer.field_renders
#audit axioms Rumoca.CTree.Printer.arguments_render
#audit axioms Rumoca.CTree.Printer.call_renders
#audit axioms Rumoca.CTree.Printer.expression_renders
