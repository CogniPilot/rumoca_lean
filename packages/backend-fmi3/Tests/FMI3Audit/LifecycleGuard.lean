import RumocaFMI3.LifecycleGuard
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.LifecycleGuard.

#audit axioms Rumoca.FMI3.LifecycleGuard.mode_code_beq
#audit axioms Rumoca.FMI3.LifecycleGuard.modes_eval
#audit axioms Rumoca.FMI3.LifecycleGuard.eval_correct
#audit axioms Rumoca.FMI3.LifecycleGuard.reference
#audit axioms Rumoca.FMI3.LifecycleGuard.require_run
#audit axioms Rumoca.FMI3.LifecycleGuard.accept
#audit axioms Rumoca.FMI3.LifecycleGuard.reject_prefix
