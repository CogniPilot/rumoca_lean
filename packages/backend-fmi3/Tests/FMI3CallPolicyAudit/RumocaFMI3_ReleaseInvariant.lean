import RumocaFMI3.ReleaseInvariant
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ReleaseInvariant.

#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.Metadata.preserved
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.MetadataFrame.refl
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.Ready.atomic_origin
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.Ready.exit_value
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.Ready.withHeap
#audit axioms Rumoca.FMI3.StaticRelease.ConcurrentInvariant.step_ready
