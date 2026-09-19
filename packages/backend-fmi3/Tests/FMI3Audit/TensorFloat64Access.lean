import RumocaFMI3.TensorFloat64Access
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorFloat64Access.

#audit axioms Rumoca.FMI3.TensorFloat64.getBody_closed
#audit axioms Rumoca.FMI3.TensorFloat64.setBody_closed
#audit axioms Rumoca.FMI3.TensorFloat64.validate_reaches
#audit axioms Rumoca.FMI3.TensorFloat64.get_reaches_of
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_time
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_state
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_deriv
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_output
#audit axioms Rumoca.FMI3.TensorFloat64.set_reaches_of
#audit axioms Rumoca.FMI3.TensorFloat64.set_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.set_behaviors_state
#audit axioms Rumoca.FMI3.TensorFloat64.null_get_behaviors
#audit axioms Rumoca.FMI3.TensorFloat64.null_set_behaviors
#audit axioms Rumoca.FMI3.TensorFloat64.reads_time
#audit axioms Rumoca.FMI3.TensorFloat64.reads_output
#audit axioms Rumoca.FMI3.TensorFloat64.writable_state
#audit axioms Rumoca.FMI3.TensorFloat64.inputWritableStore_writable
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_time
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_state
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_deriv
#audit axioms Rumoca.FMI3.TensorFloat64.get_instance_behaviors_output
#audit axioms Rumoca.FMI3.TensorFloat64.set_instance_behaviors_state
#audit axioms Rumoca.FMI3.TensorFloat64.set_instance_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.set_preserves_other_instances
#audit axioms Rumoca.FMI3.TensorFloat64.getBody_printable
#audit axioms Rumoca.FMI3.TensorFloat64.setBody_printable
#audit axioms Rumoca.FMI3.TensorFloat64.signature_printable
#audit axioms Rumoca.FMI3.TensorFloat64.getFunction_denotes
#audit axioms Rumoca.FMI3.TensorFloat64.setFunction_denotes
#audit axioms Rumoca.FMI3.TensorFloat64.get_contract
#audit axioms Rumoca.FMI3.TensorFloat64.set_contract
#audit axioms Rumoca.FMI3.TensorFloat64.get_fail_prefix
#audit axioms Rumoca.FMI3.TensorFloat64.set_fail_prefix
#audit axioms Rumoca.FMI3.TensorFloat64.get_fail_behaviors
#audit axioms Rumoca.FMI3.TensorFloat64.set_fail_behaviors
