import RumocaFMI3.TensorCallPolicy
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorCallPolicy.

#audit axioms Rumoca.FMI3.TensorCallPolicy.body_admits
#audit axioms Rumoca.FMI3.TensorCallPolicy.funcs_acceptedT
#audit axioms Rumoca.FMI3.TensorCallPolicy.acceptedT_noHeap
#audit axioms Rumoca.FMI3.TensorCallPolicy.tensor_no_heap
#audit axioms Rumoca.FMI3.TensorCallPolicy.classifiedT_rank
#audit axioms Rumoca.FMI3.TensorCallPolicy.body_rankT
#audit axioms Rumoca.FMI3.TensorCallPolicy.functions_rankT
#audit axioms Rumoca.FMI3.TensorCallPolicy.functions_isSomeT
#audit axioms Rumoca.FMI3.TensorCallPolicy.tensor_acyclic
