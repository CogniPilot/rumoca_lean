import RumocaFMI3.MEMixedConfiguration
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.MEMixedConfiguration.

#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.Stored.framed
#audit axioms Rumoca.FMI3.MEMixedRun.configuration_outside
#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.StoragePolicy.mono
#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.FramePolicy.storage
#audit axioms Rumoca.FMI3.MEMixedRun.Configuration.FramePolicy.mono
