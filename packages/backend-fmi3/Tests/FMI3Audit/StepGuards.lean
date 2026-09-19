import RumocaFMI3.StepGuards
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.StepGuards.

#audit axioms Rumoca.FMI3.StepGuards.stop_condition
#audit axioms Rumoca.FMI3.StepGuards.progress_condition
#audit axioms Rumoca.FMI3.StepGuards.grid_condition
#audit axioms Rumoca.FMI3.StepGuards.rounding_path
#audit axioms Rumoca.FMI3.StepGuards.clock_path
#audit axioms Rumoca.FMI3.StepGuards.grid_path
#audit axioms Rumoca.FMI3.StepGuards.actual_sections
#audit axioms Rumoca.FMI3.StepGuards.accepted_execution
