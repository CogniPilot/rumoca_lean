import ProofAudit.Audit
import Rumoca.Behavioral
import Rumoca.Compiler
import Rumoca.Lowering
import Rumoca.Semantics
import Rumoca.Source
import Rumoca.Verified
import Rumoca.ArrayProofs
import Rumoca.FMI3BuildProofs
import Rumoca.ParseFilesProofs
import Rumoca.Provenance

#audit axioms Rumoca.Artifact.source_locations
#audit axioms Rumoca.compile_resolve_error
#audit axioms Rumoca.compile_error_after_parse

#audit axioms Rumoca.CLI.analyze_eq_reference
#audit axioms Rumoca.CLI.analyze_json
#audit axioms Rumoca.CLI.analyze_failure
#audit axioms Rumoca.CLI.analyze_terminal
#audit axioms Rumoca.CLI.analyze_batch

#audit axioms Rumoca.FMI3.sourceBuild_correct
#audit axioms Rumoca.FMI3.lexed_name
#audit axioms Rumoca.FMI3.parsed_name
#audit axioms Rumoca.FMI3.parsed_modelIdentifier
#audit axioms Rumoca.FMI3.parsed_functionPrefix

#audit axioms Rumoca.ArrayCompiler.Prepared.source_correct
#audit axioms Rumoca.ArrayCompiler.Prepared.equation_correct
#audit axioms Rumoca.ArrayCompiler.Prepared.initialization_correct
#audit axioms Rumoca.ArrayCompiler.prepare_correct

#audit axioms Rumoca.compile_complete
#audit axioms Rumoca.compile_eq_parsed
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
