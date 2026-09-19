import RumocaFMI3.ReleaseCapture
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ReleaseCapture.

#audit axioms Rumoca.FMI3.StaticRelease.Capture.atomic_control
#audit axioms Rumoca.FMI3.StaticRelease.Capture.captured_footprint
#audit axioms Rumoca.FMI3.StaticRelease.Capture.history_protected
#audit axioms Rumoca.FMI3.StaticRelease.Capture.needsMetadata_withHeap
#audit axioms Rumoca.FMI3.StaticRelease.Capture.protected_frame
#audit axioms Rumoca.FMI3.StaticRelease.Capture.step_protected
#audit axioms Rumoca.FMI3.StaticRelease.Capture.tail_footprint
