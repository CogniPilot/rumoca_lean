import RumocaFMI3.ReleaseConcurrentInvariant
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ReleaseConcurrentInvariant.

#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.call_prefix_origin
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.thread_reaches
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.thread_step
