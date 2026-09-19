import RumocaFMI3.StaticRelease
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StaticRelease.

#audit axioms Rumoca.FMI3.StaticRelease.call_entry
#audit axioms Rumoca.FMI3.StaticRelease.guard_step
#audit axioms Rumoca.FMI3.StaticRelease.return_path
#audit axioms Rumoca.FMI3.StaticRelease.clear_entry
#audit axioms Rumoca.FMI3.StaticRelease.null_behaviors
#audit axioms Rumoca.FMI3.StaticRelease.occupied_behaviors
#audit axioms Rumoca.FMI3.StaticRelease.release_owned
