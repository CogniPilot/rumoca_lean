import RumocaFMI3.TensorDoStep
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorDoStep.

#audit axioms Rumoca.FMI3.TensorDoStep.eulerBody_closed
#audit axioms Rumoca.FMI3.TensorDoStep.eulerStep
#audit axioms Rumoca.FMI3.TensorDoStep.euler_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.euler_delivers
#audit axioms Rumoca.FMI3.TensorDoStep.store_writable_state
#audit axioms Rumoca.FMI3.TensorDoStep.internalStep_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.derivative_run
#audit axioms Rumoca.FMI3.TensorDoStep.stepBody_closed
#audit axioms Rumoca.FMI3.TensorDoStep.stepBody_noDecl
#audit axioms Rumoca.FMI3.TensorDoStep.internalStepPure_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.eulerIterate_succ
#audit axioms Rumoca.FMI3.TensorDoStep.stepLoop_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.timeStep
#audit axioms Rumoca.FMI3.TensorDoStep.stepBodyT_closed
#audit axioms Rumoca.FMI3.TensorDoStep.stepBodyT_noDecl
#audit axioms Rumoca.FMI3.TensorDoStep.internalStepPureT_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.stepLoopT_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.doStepBody_prefix
#audit axioms Rumoca.FMI3.TensorDoStep.outerLoop_closed
#audit axioms Rumoca.FMI3.TensorDoStep.doStepBody_closed
#audit axioms Rumoca.FMI3.TensorDoStep.field_index_block
#audit axioms Rumoca.FMI3.TensorDoStep.cell_block_ne
#audit axioms Rumoca.FMI3.TensorDoStep.tensorSolve_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.tensorSolveOutput_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.front_run
#audit axioms Rumoca.FMI3.TensorDoStep.accepted_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.accepted_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.accepted_output_reaches
#audit axioms Rumoca.FMI3.TensorDoStep.accepted_output_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.null_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.lifecycle_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.finishOK
#audit axioms Rumoca.FMI3.TensorDoStep.cInterface_fenv
#audit axioms Rumoca.FMI3.TensorDoStep.fenvInterface_fenv
#audit axioms Rumoca.FMI3.TensorDoStep.discard_prefix
#audit axioms Rumoca.FMI3.TensorDoStep.discard_suppressed_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.discard_logged_behaviors
#audit axioms Rumoca.FMI3.TensorDoStep.signature_printable
#audit axioms Rumoca.FMI3.TensorDoStep.body_printable
#audit axioms Rumoca.FMI3.TensorDoStep.function_denotes
#audit axioms Rumoca.FMI3.TensorDoStep.execution_free
#audit axioms Rumoca.FMI3.TensorDoStep.execution_output
#audit axioms Rumoca.FMI3.TensorDoStep.contract
