import RumocaFMI3.ConstantFloat64Access
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ConstantFloat64Access.

#audit axioms Rumoca.FMI3.ConstantFloat64.reads_noDecl
#audit axioms Rumoca.FMI3.ConstantFloat64.reads_printable
#audit axioms Rumoca.FMI3.ConstantFloat64.get_derivative_reaches
#audit axioms Rumoca.FMI3.ConstantFloat64.get_contract
