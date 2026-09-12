import Rumoca.FMI3LoggingProofs
import ProofAudit.Audit
import Rumoca.Behavioral
import Rumoca.Compiler
import Rumoca.Lowering
import Rumoca.Semantics
import Rumoca.Source
import Rumoca.Verified
import Rumoca.ArrayProofs
import Rumoca.FMI3CountProofs
import Rumoca.FMI3VersionProofs
import Rumoca.ParseFilesProofs
import Rumoca.Provenance
import Rumoca.Initialization
import Rumoca.InitializationDiagnosticProofs

#audit axioms Rumoca.Artifact.source_identity
#audit axioms Rumoca.Artifact.initializationDiagnostics_eq_forModel
#audit axioms Rumoca.Artifact.initializationDiagnostic_count
#audit axioms Rumoca.Artifact.initializationDiagnostic_state
#audit axioms Rumoca.Source.initializes_iff
#audit axioms Rumoca.Flat.Model.initialization_matches
#audit axioms Rumoca.DAE.Model.initialization_matches
#audit axioms Rumoca.Solve.Model.initialization_checked_real
#audit axioms Rumoca.Solve.Model.initialization_correct
#audit axioms Rumoca.Solve.Model.initialized_solution_unique
#audit axioms Rumoca.Solve.FMI3Model.initialization_matches
#audit axioms Rumoca.GALEC.initialization_matches

#audit axioms Rumoca.Artifact.source_locations
#audit axioms Rumoca.compile_resolve_error
#audit axioms Rumoca.compile_error_after_parse

#audit axioms Rumoca.CLI.analyze_eq_reference
#audit axioms Rumoca.CLI.analyze_json
#audit axioms Rumoca.CLI.analyze_failure
#audit axioms Rumoca.CLI.analyze_terminal
#audit axioms Rumoca.CLI.analyze_batch

#audit axioms Rumoca.FMI3.counts_source
#audit axioms Rumoca.FMI3.counts_failure_source
#audit axioms Rumoca.FMI3.version_source
#audit axioms Rumoca.FMI3.sourceBuild_correct
#audit axioms Rumoca.FMI3.reset_result
#audit axioms Rumoca.FMI3.reset_source
#audit axioms Rumoca.FMI3.compile_reset_verified
#audit axioms Rumoca.FMI3.compile_rendered_reset_verified
#audit axioms Rumoca.FMI3.adapter_chars
#audit axioms Rumoca.FMI3.adapter_correct
#audit axioms Rumoca.FMI3.adapter_preprocessed
#audit axioms Rumoca.FMI3.adapter_reset_syntax
#audit axioms Rumoca.FMI3.adapter_reset_tokenization
#audit axioms Rumoca.FMI3.adapter_functions_tokenization
#audit axioms Rumoca.FMI3.adapter_call_entry
#audit axioms Rumoca.FMI3.adapter_reset_source
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

#audit axioms Rumoca.FMI3.logging_source
