import RumocaFMI3.TensorCountQueries
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorCountQueries.

#audit axioms Rumoca.CMemory.store_of_convert
#audit axioms Rumoca.FMI3.TensorCountQueries.count_bounded
#audit axioms Rumoca.FMI3.TensorCountQueries.body_closed
#audit axioms Rumoca.FMI3.TensorCountQueries.parameters_bound
#audit axioms Rumoca.FMI3.TensorCountQueries.store_count
#audit axioms Rumoca.FMI3.TensorCountQueries.pointer_pass
#audit axioms Rumoca.FMI3.TensorCountQueries.body_run
#audit axioms Rumoca.FMI3.TensorCountQueries.call_behaviors
#audit axioms Rumoca.FMI3.TensorCountQueries.null_behaviors
#audit axioms Rumoca.FMI3.TensorCountQueries.signature_printable
#audit axioms Rumoca.FMI3.TensorCountQueries.body_printable
#audit axioms Rumoca.FMI3.TensorCountQueries.function_denotes
#audit axioms Rumoca.FMI3.TensorCountQueries.contract
