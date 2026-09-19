import RumocaC.StatementPrinter
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.StatementPrinter.

#audit axioms Rumoca.CTree.Printer.declare_renders
#audit axioms Rumoca.CTree.Printer.assign_renders
#audit axioms Rumoca.CTree.Printer.eval_renders
#audit axioms Rumoca.CTree.Printer.return_void_renders
#audit axioms Rumoca.CTree.Printer.return_value_renders
#audit axioms Rumoca.CTree.Printer.items_render
#audit axioms Rumoca.CTree.Printer.while_renders
#audit axioms Rumoca.CTree.Printer.if_then_renders
#audit axioms Rumoca.CTree.Printer.if_else_renders
#audit axioms Rumoca.CTree.Printer.statement_renders
