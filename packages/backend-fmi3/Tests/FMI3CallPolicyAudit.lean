import RumocaFMI3.RuntimeLinkage
import RumocaFMI3.CallPolicy
import ProofAudit.Audit

/-! Independently cached formal audits for the call policy; no example-based tests. -/

#audit axioms Rumoca.FMI3.CallPolicy.body_policy
#audit axioms Rumoca.FMI3.CallPolicy.helpers_policy
#audit axioms Rumoca.FMI3.CallPolicy.functions_policy
#audit axioms Rumoca.FMI3.CallPolicy.classified_rank
#audit axioms Rumoca.FMI3.CallPolicy.body_rank
#audit axioms Rumoca.FMI3.CallPolicy.helpers_rank
#audit axioms Rumoca.FMI3.CallPolicy.functions_rank
#audit axioms Rumoca.FMI3.CallPolicy.entry_rank
#audit axioms Rumoca.FMI3.CallPolicy.covered_ranks
#audit axioms Rumoca.FMI3.CallPolicy.program_tree_name
#audit axioms Rumoca.FMI3.CallPolicy.program_rank
#audit axioms Rumoca.FMI3.CallPolicy.complete_program_no_cycle

#audit axioms Rumoca.FMI3.RuntimeLinkage.linked_contract
#audit axioms Rumoca.FMI3.RuntimeLinkage.logged_call_decreases
#audit axioms Rumoca.FMI3.RuntimeLinkage.logged_contract
#audit axioms Rumoca.FMI3.RuntimeLinkage.logged_execution_depth
#audit axioms Rumoca.FMI3.RuntimeLinkage.rank_bounded
#audit axioms Rumoca.FMI3.RuntimeLinkage.static_fresh
#audit axioms Rumoca.FMI3.RuntimeLinkage.static_unranked
#audit axioms Rumoca.FMI3.RuntimeLinkage.unranked_undefined
#audit axioms Rumoca.FMI3.RuntimeLinkage.withLogger_contract
