import RumocaFMI3.ConstantDoStep
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.ConstantDoStep.

#audit axioms Rumoca.FMI3.ConstantDoStep.doStepBody_prefix
#audit axioms Rumoca.FMI3.ConstantDoStep.doStepBody_closed
#audit axioms Rumoca.FMI3.ConstantDoStep.function_denotes
#audit axioms Rumoca.FMI3.ConstantDoStep.null_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.lifecycle_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.cInterface_fenv
#audit axioms Rumoca.FMI3.ConstantDoStep.fenvInterface_fenv
#audit axioms Rumoca.FMI3.ConstantDoStep.constant_step_enter
#audit axioms Rumoca.FMI3.ConstantDoStep.internalStep_reaches
#audit axioms Rumoca.FMI3.ConstantDoStep.stepLoop_reaches
#audit axioms Rumoca.FMI3.ConstantDoStep.solve_reaches
#audit axioms Rumoca.FMI3.ConstantDoStep.front_run
#audit axioms Rumoca.FMI3.ConstantDoStep.accepted_reaches
#audit axioms Rumoca.FMI3.ConstantDoStep.accepted_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.execution_free
#audit axioms Rumoca.FMI3.ConstantDoStep.discard_prefix
#audit axioms Rumoca.FMI3.ConstantDoStep.discard_suppressed_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.discard_logged_behaviors
#audit axioms Rumoca.FMI3.ConstantDoStep.contract
