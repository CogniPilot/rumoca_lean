import RumocaC.BooleanProofs
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.BooleanProofs.

#audit axioms Rumoca.CBody.BoolProofs.eval_and
#audit axioms Rumoca.CBody.BoolProofs.eval_or
#audit axioms Rumoca.CBody.BoolProofs.eval_not
#audit axioms Rumoca.CTree.Expr.disjunction
#audit axioms Rumoca.CBody.BoolProofs.eval_disjunction
#audit axioms Rumoca.CTree.Expr.nonfinite
#audit axioms Rumoca.CBody.evalWith_nonfinite
