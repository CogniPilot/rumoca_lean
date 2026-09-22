import RumocaFMI3.TensorFunctions
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorFunctions.

#audit axioms Rumoca.FMI3.TensorFunctions.tensorFunction_signature
#audit axioms Rumoca.FMI3.TensorFunctions.tensorFunction_name
#audit axioms Rumoca.FMI3.TensorFunctions.functions_names
#audit axioms Rumoca.FMI3.TensorFunctions.functions_signatures
#audit axioms Rumoca.FMI3.TensorFunctions.functions_nodup
#audit axioms Rumoca.FMI3.TensorFunctions.rendered_functions
#audit axioms Rumoca.FMI3.TensorFunctions.rendered_member
#audit axioms Rumoca.FMI3.TensorFunctions.rendered_helper
#audit axioms Rumoca.FMI3.TensorFunctions.definition_bound
#audit axioms Rumoca.FMI3.TensorFunctions.function_bound
#audit axioms Rumoca.FMI3.TensorFunctions.program_covered
#audit axioms Rumoca.FMI3.TensorFunctions.helpers_bound
#audit axioms Rumoca.FMI3.TensorFunctions.doStep_bound
#audit axioms Rumoca.FMI3.TensorFunctions.doStep_fragment
#audit axioms Rumoca.FMI3.TensorFunctions.header_fresh
#audit axioms Rumoca.FMI3.TensorFunctions.text_bound
#audit axioms Rumoca.FMI3.TensorFunctions.pool_complete
#audit axioms Rumoca.FMI3.TensorFunctions.helpers_subset
#audit axioms Rumoca.FMI3.TensorFunctions.scalar_names
#audit axioms Rumoca.FMI3.TensorFunctions.helper_names_sublist
#audit axioms Rumoca.FMI3.TensorFunctions.kernel_entry_resolves
#audit axioms Rumoca.FMI3.TensorFunctions.kernel_entry_is_kernel
#audit axioms Rumoca.FMI3.TensorFunctions.kernel_prototype_matches_args
#audit axioms Rumoca.FMI3.TensorFunctions.jacobian_prototype_matches_args
