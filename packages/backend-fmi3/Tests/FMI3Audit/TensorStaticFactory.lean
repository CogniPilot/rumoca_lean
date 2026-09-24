import RumocaFMI3.TensorStaticFactory
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.TensorStaticFactory.

#audit axioms Rumoca.FMI3.TensorFactory.reserve_entry
#audit axioms Rumoca.FMI3.TensorFactory.initialization_reaches
#audit axioms Rumoca.FMI3.TensorFactory.guarded_initialization
#audit axioms Rumoca.FMI3.TensorFactory.successful
#audit axioms Rumoca.FMI3.TensorFactory.exhausted_silent
#audit axioms Rumoca.FMI3.TensorFactory.initialized_owners
#audit axioms Rumoca.FMI3.TensorFactory.successful_owned
#audit axioms Rumoca.FMI3.TensorFactory.Created.release
#audit axioms Rumoca.FMI3.TensorFactory.create_release
#audit axioms Rumoca.FMI3.TensorFactory.admission_accepts
#audit axioms Rumoca.FMI3.TensorFactory.rejected_silent
#audit axioms Rumoca.FMI3.TensorFactory.contract

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.TensorFactory.FunctionContract
#audit axioms Rumoca.FMI3.TensorFactory.FunctionContractWith
#audit axioms Rumoca.FMI3.TensorFactory.LogicalFunctionContract
#audit axioms Rumoca.FMI3.TensorFactory.admission_accepts_with
#audit axioms Rumoca.FMI3.TensorFactory.code
#audit axioms Rumoca.FMI3.TensorFactory.codeWith
#audit axioms Rumoca.FMI3.TensorFactory.contract_explicit
#audit axioms Rumoca.FMI3.TensorFactory.contract_with
#audit axioms Rumoca.FMI3.TensorFactory.exhausted_silent_explicit
#audit axioms Rumoca.FMI3.TensorFactory.exhausted_silent_with
#audit axioms Rumoca.FMI3.TensorFactory.exhaustion_path
#audit axioms Rumoca.FMI3.TensorFactory.exhaustion_path_with
#audit axioms Rumoca.FMI3.TensorFactory.function
#audit axioms Rumoca.FMI3.TensorFactory.functionWith
#audit axioms Rumoca.FMI3.TensorFactory.guarded_initialization_with
#audit axioms Rumoca.FMI3.TensorFactory.logicalCode
#audit axioms Rumoca.FMI3.TensorFactory.logicalFunction
#audit axioms Rumoca.FMI3.TensorFactory.rejected_silent_with
#audit axioms Rumoca.FMI3.TensorFactory.reserve_entry_with
#audit axioms Rumoca.FMI3.TensorFactory.reserve_resume
#audit axioms Rumoca.FMI3.TensorFactory.reserve_resume_with
#audit axioms Rumoca.FMI3.TensorFactory.successful_with
