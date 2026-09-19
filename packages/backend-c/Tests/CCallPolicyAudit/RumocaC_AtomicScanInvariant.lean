import RumocaC.AtomicScanInvariant
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.AtomicScanInvariant.

#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.Ready.call_origin
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.Ready.exit_value
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.Ready.withHeap
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.loop_prefix_bounds
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.step_ready
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.thread_reaches
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.thread_step
