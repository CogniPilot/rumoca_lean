import RumocaFMI3.TensorInstanceStorage
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorInstanceStorage.

#audit axioms Rumoca.FMI3.TensorInstance.reads_state
#audit axioms Rumoca.FMI3.TensorInstance.reads_input
#audit axioms Rumoca.FMI3.TensorInstance.writable_derivative
#audit axioms Rumoca.FMI3.TensorInstance.fields_separate
#audit axioms Rumoca.FMI3.TensorInstance.instances_separate
#audit axioms Rumoca.FMI3.TensorInstance.store_other_instance
#audit axioms Rumoca.FMI3.TensorInstance.writable_output
#audit axioms Rumoca.FMI3.TensorInstance.core_eq_opt
#audit axioms Rumoca.FMI3.TensorInstance.store_eq_opt
#audit axioms Rumoca.FMI3.TensorInstance.coreOpt_none
#audit axioms Rumoca.FMI3.TensorInstance.constantStore_eq_opt
#audit axioms Rumoca.FMI3.TensorInstance.constant_reads_state
#audit axioms Rumoca.FMI3.TensorInstance.constant_writable_derivative
#audit axioms Rumoca.FMI3.TensorInstance.constant_fields_separate
#audit axioms Rumoca.FMI3.TensorInstance.constant_instances_separate
#audit axioms Rumoca.FMI3.TensorInstance.constant_store_other_instance
