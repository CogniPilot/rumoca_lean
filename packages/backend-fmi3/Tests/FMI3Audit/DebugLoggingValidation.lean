import RumocaFMI3.DebugLoggingValidation
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.DebugLoggingValidation.

-- Explicit-null migration: shared syntax, retained domains and typed execution.
#audit axioms Rumoca.FMI3.DebugLogging.missingWith
#audit axioms Rumoca.FMI3.DebugLogging.rejectNullWith
#audit axioms Rumoca.FMI3.DebugLogging.iterationWith
#audit axioms Rumoca.FMI3.DebugLogging.validationWith
#audit axioms Rumoca.FMI3.DebugLogging.codeWith
#audit axioms Rumoca.FMI3.DebugLogging.logicalMissing
#audit axioms Rumoca.FMI3.DebugLogging.logicalRejectNull
#audit axioms Rumoca.FMI3.DebugLogging.logicalIteration
#audit axioms Rumoca.FMI3.DebugLogging.logicalValidation
#audit axioms Rumoca.FMI3.DebugLogging.logicalCode
#audit axioms Rumoca.FMI3.DebugLogging.explicitMissing
#audit axioms Rumoca.FMI3.DebugLogging.PointerMissingLaw
#audit axioms Rumoca.FMI3.DebugLogging.PointerMissingLaw.mk
#audit axioms Rumoca.FMI3.DebugLogging.PointerMissingLaw.value
#audit axioms Rumoca.FMI3.DebugLogging.PointerMissingLaw.condition
#audit axioms Rumoca.FMI3.DebugLogging.logical_missing_law
#audit axioms Rumoca.FMI3.DebugLogging.explicit_missing_law
#audit axioms Rumoca.FMI3.DebugLogging.iteration_closed_with
#audit axioms Rumoca.FMI3.DebugLogging.null_category_step_with
#audit axioms Rumoca.FMI3.DebugLogging.null_category_step_explicit
#audit axioms Rumoca.FMI3.DebugLogging.iteration_valid_equivalence_with
#audit axioms Rumoca.FMI3.DebugLogging.iteration_valid_equivalence_explicit
#audit axioms Rumoca.FMI3.DebugLogging.missing
#audit axioms Rumoca.FMI3.DebugLogging.rejectNull
#audit axioms Rumoca.FMI3.DebugLogging.iteration
#audit axioms Rumoca.FMI3.DebugLogging.validation
#audit axioms Rumoca.FMI3.DebugLogging.code

#audit axioms Rumoca.FMI3.DebugLogging.iteration_closed
#audit axioms Rumoca.FMI3.DebugLogging.category_eval
#audit axioms Rumoca.FMI3.DebugLogging.null_category_step
#audit axioms Rumoca.FMI3.DebugLogging.difference_step
#audit axioms Rumoca.FMI3.DebugLogging.iteration_valid_equivalence
