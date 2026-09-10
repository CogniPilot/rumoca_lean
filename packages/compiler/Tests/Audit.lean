import ProofAudit.Audit
import Rumoca.Behavioral
import Rumoca.Compiler
import Rumoca.Lowering
import Rumoca.Semantics
import Rumoca.Source
import Rumoca.Verified
import Rumoca.ArrayProofs

#audit axioms Rumoca.ArrayCompiler.Prepared.source_correct
#audit axioms Rumoca.ArrayCompiler.Prepared.equation_correct
#audit axioms Rumoca.ArrayCompiler.Prepared.initialization_correct
#audit axioms Rumoca.ArrayCompiler.prepare_correct

#audit axioms Rumoca.compile_complete
#audit axioms Rumoca.flatten_correct
#audit axioms Rumoca.dae_correct
#audit axioms Rumoca.solve_correct
#audit axioms Rumoca.compiler_correct
#audit axioms Rumoca.ideal_samples_refine_solution
#audit axioms Rumoca.ideal_end_to_end
#audit axioms Rumoca.emitted_text_is_unit
#audit axioms Rumoca.execution_correct
#audit axioms Rumoca.artifact_correct
#audit axioms Rumoca.compile_verified
#audit axioms Rumoca.Flat.lower_correct
#audit axioms Rumoca.DAE.lower_correct
#audit axioms Rumoca.Solve.lower_correct
#audit axioms Rumoca.lowering_chain_correct
#audit axioms Rumoca.Source.solution_unique
#audit axioms Rumoca.Source.rounded_samples_unique
#audit axioms Rumoca.Solve.lower_samples_correct
#audit axioms Rumoca.CStatements.lower_behavior_correct
#audit axioms Rumoca.CStatements.real_refinement
#audit axioms Rumoca.compiler_semantic_preservation
#audit axioms Rumoca.Flat.behavior_correct
#audit axioms Rumoca.DAE.behavior_correct
#audit axioms Rumoca.Solve.behavior_correct
#audit axioms Rumoca.CStatements.solve_behavior_correct
#audit axioms Rumoca.lowering_chain_behavior_correct
#audit axioms Rumoca.compiler_preserves_property
#audit axioms Rumoca.CStatements.model_exchange_correct
#audit axioms Rumoca.CStatements.co_simulation_correct
