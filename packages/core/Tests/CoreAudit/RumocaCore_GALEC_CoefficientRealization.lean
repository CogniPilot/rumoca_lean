import RumocaCore.GALEC.CoefficientRealization
import ProofAudit.Audit

-- Every explicitly authored declaration in the corresponding source module.
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.eval
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.pointwise
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.pointwise_get
#audit axioms Rumoca.GALEC.Coefficients.EvaluatorRealization
#audit axioms Rumoca.GALEC.Coefficients.EvaluatorRealization.diagonal_correct
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.inDomain
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.Executes
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.executes_iff
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.Writes
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.write_iff
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.scatter_executes_iff
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.pointwise_executes_iff
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.Materializes
#audit axioms Rumoca.GALEC.Coefficients.ScalarExpr.materializes_iff
#audit axioms Rumoca.GALEC.Coefficients.FiniteRealization
#audit axioms Rumoca.GALEC.Coefficients.FiniteRealization.executes_iff
#audit axioms Rumoca.GALEC.Coefficients.FiniteRealization.result_exact
#audit axioms Rumoca.GALEC.Coefficients.FiniteRealization.materializes_iff
