import RumocaFMI3.TensorFloat64Access
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorFloat64Access.

#audit axioms Rumoca.FMI3.TensorFloat64.basicReject
#audit axioms Rumoca.FMI3.TensorFloat64.basic_condition_eq
#audit axioms Rumoca.FMI3.TensorFloat64.basic_explicit_pass
#audit axioms Rumoca.FMI3.TensorFloat64.guard_reaches
#audit axioms Rumoca.FMI3.TensorFloat64.set_guard_reaches

#audit axioms Rumoca.FMI3.TensorFloat64.getBody_closed
#audit axioms Rumoca.FMI3.TensorFloat64.setBody_closed
#audit axioms Rumoca.FMI3.TensorFloat64.validate_reaches
#audit axioms Rumoca.FMI3.TensorFloat64.get_reaches_of
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_time
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_input
#audit axioms Rumoca.FMI3.TensorFloat64.get_behaviors_state
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
#audit axioms Rumoca.FMI3.TensorFloat64.getBodyFor_printable
#audit axioms Rumoca.FMI3.TensorFloat64.setBodyFor_printable
#audit axioms Rumoca.FMI3.TensorFloat64.validateBody
#audit axioms Rumoca.FMI3.TensorFloat64.validate_step
#audit axioms Rumoca.FMI3.TensorFloat64.derivativeArm_noDecl
#audit axioms Rumoca.FMI3.TensorFloat64.guard_reaches_for
#audit axioms Rumoca.FMI3.TensorFloat64.declares_reaches_for
#audit axioms Rumoca.FMI3.TensorFloat64.rhs_read_enter
#audit axioms Rumoca.FMI3.TensorFloat64.jacobian_read_enter
#audit axioms Rumoca.FMI3.TensorFloat64.resume_discard
#audit axioms Rumoca.FMI3.TensorFloat64.get_deriv_reaches
#audit axioms Rumoca.FMI3.TensorFloat64.get_output_reaches
#audit axioms Rumoca.FMI3.TensorFloat64.rhsCall_printable
#audit axioms Rumoca.FMI3.TensorFloat64.jacobianCall_printable
