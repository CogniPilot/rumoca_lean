import RumocaFMI3.ArrayAccess
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ArrayAccess.

#audit axioms Rumoca.FMI3.ArrayAccess.getter_guard
#audit axioms Rumoca.FMI3.ArrayAccess.setter_guard
#audit axioms Rumoca.FMI3.ArrayAccess.run_guard
#audit axioms Rumoca.FMI3.ArrayAccess.explicitGuard
#audit axioms Rumoca.FMI3.ArrayAccess.run_explicit_guard
#audit axioms Rumoca.FMI3.ArrayAccess.run_explicit_guard_zero

#audit axioms Rumoca.FMI3.ArrayAccess.countGuard
#audit axioms Rumoca.FMI3.ArrayAccess.count_condition_eval
#audit axioms Rumoca.FMI3.ArrayAccess.count_guard_next
#audit axioms Rumoca.FMI3.ArrayAccess.run_count_guard
#audit axioms Rumoca.FMI3.ArrayAccess.run_count_guard_zero
#audit axioms Rumoca.FMI3.ArrayAccess.float64Guard
