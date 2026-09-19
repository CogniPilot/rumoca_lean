import RumocaFMI3.ConstantCallPolicy
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ConstantCallPolicy.

#audit axioms Rumoca.FMI3.ConstantCallPolicy.body_admits
#audit axioms Rumoca.FMI3.ConstantCallPolicy.funcs_acceptedC
#audit axioms Rumoca.FMI3.ConstantCallPolicy.acceptedC_noHeap
#audit axioms Rumoca.FMI3.ConstantCallPolicy.constant_no_heap
#audit axioms Rumoca.FMI3.ConstantCallPolicy.classifiedC_rank
#audit axioms Rumoca.FMI3.ConstantCallPolicy.body_rankC
#audit axioms Rumoca.FMI3.ConstantCallPolicy.functions_rankC
#audit axioms Rumoca.FMI3.ConstantCallPolicy.functions_isSomeC
#audit axioms Rumoca.FMI3.ConstantCallPolicy.constant_acyclic
