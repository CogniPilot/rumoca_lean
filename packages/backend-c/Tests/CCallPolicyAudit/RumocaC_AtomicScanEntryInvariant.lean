import RumocaC.AtomicScanEntryInvariant
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.AtomicScanEntryInvariant.

#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.FullReady.atomic_origin
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.FullReady.exit_value
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.FullReady.withHeap
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.call_prefix_bounds
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.full_step_ready
#audit axioms Rumoca.CAtomicScan.ConcurrentInvariant.full_thread_reaches
