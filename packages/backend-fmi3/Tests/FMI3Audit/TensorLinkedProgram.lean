import RumocaFMI3.TensorLinkedProgram
import ProofAudit.Audit

-- Generic explicit-table assembly and square specialization. Integration into
-- the existing audit aggregator belongs to the single candidate's owner.
#audit axioms Rumoca.FMI3.TensorFunctions.append_unique
#audit axioms Rumoca.FMI3.TensorFunctions.linked_numerical
#audit axioms Rumoca.FMI3.TensorFunctions.linked_adapter
#audit axioms Rumoca.FMI3.TensorFunctions.linked_no_kernel
#audit axioms Rumoca.FMI3.TensorFunctions.public_kernel_separate
#audit axioms Rumoca.FMI3.TensorFunctions.square_names_disjoint
#audit axioms Rumoca.FMI3.TensorFunctions.combined_unique
#audit axioms Rumoca.FMI3.TensorFunctions.linked_numerical_covered
#audit axioms Rumoca.FMI3.TensorFunctions.square_linked_adapter
#audit axioms Rumoca.FMI3.TensorFunctions.square_linked_no_kernel
