import RumocaC.ConcurrentCalls
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.ConcurrentCalls.

#audit axioms Rumoca.CCalls.Concurrent.resumes_result
#audit axioms Rumoca.CCalls.Concurrent.other_thread
#audit axioms Rumoca.CCalls.Concurrent.reaches_readonly
