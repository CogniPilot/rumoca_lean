import RumocaFMI3.LoggingCapabilityFrames
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.LoggingCapabilityFrames.

#audit axioms Rumoca.FMI3.Logging.Capability.initialization_control
#audit axioms Rumoca.FMI3.Logging.Capability.me_control
#audit axioms Rumoca.FMI3.Logging.Capability.Configured.mode_written
#audit axioms Rumoca.FMI3.Logging.Capability.Failure.returned
#audit axioms Rumoca.FMI3.Logging.Capability.Failure.progress
