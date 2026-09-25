import RumocaFMI3.InstanceQuery
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.InstanceQuery.

#audit axioms Rumoca.FMI3.InstanceQuery.Request.Separate.rebase
#audit axioms Rumoca.FMI3.InstanceQuery.Request.Storage.preserved
#audit axioms Rumoca.FMI3.InstanceQuery.Request.caller_block
#audit axioms Rumoca.FMI3.InstanceQuery.Request.cs_state
#audit axioms Rumoca.FMI3.InstanceQuery.Request.not_record
#audit axioms Rumoca.FMI3.InstanceQuery.Request.step
#audit axioms Rumoca.FMI3.InstanceQuery.expected_solve
#audit axioms Rumoca.FMI3.InstanceQuery.terminated_instance
