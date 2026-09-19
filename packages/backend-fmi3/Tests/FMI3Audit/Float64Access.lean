import RumocaFMI3.Float64Access
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.Float64Access.

#audit axioms Rumoca.FMI3.Float64Access.Instance.mode_loaded
#audit axioms Rumoca.FMI3.Float64Access.Instance.represented
#audit axioms Rumoca.FMI3.Float64Access.instance_outside
#audit axioms Rumoca.FMI3.Float64Access.Instance.changed
#audit axioms Rumoca.FMI3.Float64Access.Request.prepare_frame
#audit axioms Rumoca.FMI3.Float64Access.Request.prepare_correct
#audit axioms Rumoca.FMI3.Float64Access.Request.prepared_instance
#audit axioms Rumoca.FMI3.Float64Access.Request.prepared_references
#audit axioms Rumoca.FMI3.Float64Access.Request.volume
#audit axioms Rumoca.FMI3.Float64Access.Request.after_frame
#audit axioms Rumoca.FMI3.Float64Access.assigned_final
#audit axioms Rumoca.FMI3.Float64Access.assigned_correct
#audit axioms Rumoca.FMI3.Float64Access.step
