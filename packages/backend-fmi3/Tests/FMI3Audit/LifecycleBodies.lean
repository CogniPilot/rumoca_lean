import RumocaFMI3.LifecycleBodies
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.LifecycleBodies.

#audit axioms Rumoca.FMI3.LifecycleBodies.write_frame
#audit axioms Rumoca.FMI3.LifecycleBodies.write_mode
#audit axioms Rumoca.FMI3.LifecycleBodies.write_run
#audit axioms Rumoca.FMI3.LifecycleBodies.write_history
#audit axioms Rumoca.FMI3.LifecycleBodies.write_model
#audit axioms Rumoca.FMI3.LifecycleBodies.failure_mode_run
#audit axioms Rumoca.FMI3.LifecycleBodies.terminate_run
#audit axioms Rumoca.FMI3.LifecycleBodies.terminate_correct

#audit axioms Rumoca.FMI3.LifecycleBodies.writeMode_readonly
