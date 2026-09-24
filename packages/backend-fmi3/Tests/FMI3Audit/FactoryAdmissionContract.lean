import RumocaFMI3.FactoryAdmissionContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.FactoryAdmissionContract.

#audit axioms Rumoca.FMI3.FactoryAdmission.execution_correct
#audit axioms Rumoca.FMI3.FactoryAdmission.prepared_correct
#audit axioms Rumoca.FMI3.FactoryAdmission.rendered_contract

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.FactoryAdmission.ExecutionContract
#audit axioms Rumoca.FMI3.FactoryAdmission.FunctionContract
#audit axioms Rumoca.FMI3.FactoryAdmission.PreparedContract
