import RumocaCore.GALEC.BoundedIteration
import ProofAudit.Audit

-- Every explicitly authored declaration in the corresponding source module.
#audit axioms Rumoca.GALEC.Iteration.runPrefix
#audit axioms Rumoca.GALEC.Iteration.run
#audit axioms Rumoca.GALEC.Iteration.Executes
#audit axioms Rumoca.GALEC.Iteration.Executes.bounded
#audit axioms Rumoca.GALEC.Iteration.executes_reindex
#audit axioms Rumoca.GALEC.Iteration.prefix_correct
#audit axioms Rumoca.GALEC.Iteration.run_correct
#audit axioms Rumoca.GALEC.Iteration.prefix_guarded_correct
#audit axioms Rumoca.GALEC.Iteration.run_guarded_correct
#audit axioms Rumoca.GALEC.Iteration.prefix_invariant
#audit axioms Rumoca.GALEC.Iteration.prefix_frame
#audit axioms Rumoca.GALEC.Iteration.one_based_bounds
