import RumocaFMI3.TensorFamilyContracts
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorFamilyContracts.

#audit axioms Rumoca.FMI3.absent_function
#audit axioms Rumoca.FMI3.capability_function
#audit axioms Rumoca.FMI3.scheduled_function
#audit axioms Rumoca.FMI3.scalar_bound
#audit axioms Rumoca.FMI3.scalar_member
#audit axioms Rumoca.FMI3.TensorAbsentVariables.prepared_correct
#audit axioms Rumoca.FMI3.TensorAbsentVariables.rendered_contract
#audit axioms Rumoca.FMI3.TensorAbsentVariables.family_correct
#audit axioms Rumoca.FMI3.TensorCapabilityRejection.prepared_correct
#audit axioms Rumoca.FMI3.TensorCapabilityRejection.rendered_contract
#audit axioms Rumoca.FMI3.TensorCapabilityRejection.family_correct
