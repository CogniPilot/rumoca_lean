import RumocaC.Execution
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.Execution.

#audit axioms Rumoca.CExecution.rhs_eval
#audit axioms Rumoca.CExecution.step_eval
#audit axioms Rumoca.CExecution.step_deterministic
#audit axioms Rumoca.CExecution.sample_reaches
#audit axioms Rumoca.CExecution.sample_accessible
#audit axioms Rumoca.CExecution.sample_all_executions
#audit axioms Rumoca.CExecution.sample_result_unique
#audit axioms Rumoca.CExecution.counter_in_range
