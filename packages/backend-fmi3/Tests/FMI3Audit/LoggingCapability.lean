import RumocaFMI3.LoggingCapability
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.LoggingCapability.

#audit axioms Rumoca.FMI3.Logging.Capability.requires_mono
#audit axioms Rumoca.FMI3.Logging.Capability.requires_and
#audit axioms Rumoca.FMI3.Logging.Capability.Stored.framed
#audit axioms Rumoca.FMI3.Logging.Capability.Stored.logging_written
#audit axioms Rumoca.FMI3.Logging.Capability.Stored.mode_written
#audit axioms Rumoca.FMI3.Logging.Capability.Configured.logging_written
#audit axioms Rumoca.FMI3.Logging.Capability.Configured.framed
