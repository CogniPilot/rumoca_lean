import RumocaC.TensorSumPreflightContract
import ProofAudit.Audit

#audit axioms Rumoca.CTensor.SumPreflight.value
#audit axioms Rumoca.CTensor.SumPreflight.function
#audit axioms Rumoca.CTensor.SumPreflight.result
#audit axioms Rumoca.CTensor.SumPreflight.result_get
#audit axioms Rumoca.CTensor.SumPreflight.result_allFinite
#audit axioms Rumoca.CTensor.SumPreflight.result_overflow
#audit axioms Rumoca.CTensor.SumPreflight.evaluates
#audit axioms Rumoca.CTensor.SumPreflight.call_reaches
#audit axioms Rumoca.CTensor.SumPreflight.call_correct
#audit axioms Rumoca.CTensor.SumPreflight.Syntax.tokens
#audit axioms Rumoca.CTensor.SumPreflight.Syntax.Denotes
#audit axioms Rumoca.CTensor.SumPreflight.Syntax.render_denotes
#audit axioms Rumoca.CTensor.SumPreflight.ArtifactContract
#audit axioms Rumoca.CTensor.SumPreflight.artifact_correct
