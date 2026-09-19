import Rumoca.TensorProduction
import ProofAudit.Audit

-- Axiom audit for the roots defined in Rumoca.TensorProduction.

#audit axioms Rumoca.tensorSourceBuild_correct
#audit axioms Rumoca.compileTensor_eq
#audit axioms Rumoca.compileTensor_eq_parsed
#audit axioms Rumoca.compileTensor_complete
#audit axioms Rumoca.TensorArtifact.ast_determined
#audit axioms Rumoca.TensorArtifact.tensorModel_square
#audit axioms Rumoca.TensorArtifact.name_square
#audit axioms Rumoca.TensorKernel.chars
