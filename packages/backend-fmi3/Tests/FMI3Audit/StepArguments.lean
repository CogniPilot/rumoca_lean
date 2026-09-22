import RumocaFMI3.StepArguments
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StepArguments.

#audit axioms Rumoca.FMI3.StepArguments.outputs_prefix
#audit axioms Rumoca.FMI3.StepArguments.Storage.instance_frame
#audit axioms Rumoca.FMI3.StepArguments.Storage.load_field
#audit axioms Rumoca.FMI3.StepArguments.input_prefix
#audit axioms Rumoca.FMI3.StepArguments.input_instance_frame
#audit axioms Rumoca.FMI3.StepArguments.output_cases
#audit axioms Rumoca.FMI3.StepArguments.outputs_suppressed
#audit axioms Rumoca.FMI3.StepArguments.outputs_logged
#audit axioms Rumoca.FMI3.StepArguments.input_suppressed
#audit axioms Rumoca.FMI3.StepArguments.input_logged
#audit axioms Rumoca.FMI3.StepArguments.ready_prefix
#audit axioms Rumoca.FMI3.StepArguments.pointer_condition
#audit axioms Rumoca.FMI3.StepArguments.pointerCheck_run
#audit axioms Rumoca.FMI3.StepArguments.outputs_prefix_for_tail
#audit axioms Rumoca.FMI3.StepArguments.input_prefix_for_tail
#audit axioms Rumoca.FMI3.StepArguments.context_input_silent_for_tail
#audit axioms Rumoca.FMI3.StepArguments.context_input_logged_for_tail
#audit axioms Rumoca.FMI3.StepArguments.input_missing_context
#audit axioms Rumoca.FMI3.StepArguments.input_rejection_contract
#audit axioms Rumoca.FMI3.StepArguments.output_rejection_contract
#audit axioms Rumoca.FMI3.StepArguments.scalar_input_contract
#audit axioms Rumoca.FMI3.StepArguments.scalar_output_contract
#audit axioms Rumoca.FMI3.StepArguments.ready_prefix_for_tail

#audit axioms Rumoca.FMI3.StepArguments.Storage.output_readonly
#audit axioms Rumoca.FMI3.StepArguments.Storage.error_readonly
#audit axioms Rumoca.FMI3.StepArguments.Storage.literal_at_output
#audit axioms Rumoca.FMI3.StepArguments.Storage.literal_at_error
