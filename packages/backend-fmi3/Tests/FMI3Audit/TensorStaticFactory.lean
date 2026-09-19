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
