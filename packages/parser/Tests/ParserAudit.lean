import Parser
import Parser.LocatedCompleteness
import Parser.LALR.FirstProofs
import Parser.LALR.ItemCheck
import Parser.LALR.Execution
import Parser.LALR.DerivationTrees
import Parser.LALR.Completeness
import Parser.LALR.Fuel
import Parser.LALR.Progress
import Parser.LALR.RuntimeProofs
import Parser.LALR.SafetyProofs
import Parser.Automaton
import Parser.Alphabet
import Parser.Provenance
import Parser.ProvenanceExtension
import Parser.ProvenanceMapping
import Parser.ScannerSpelling
import Parser.ScannerRefinement
import Parser.LocatedProofs
import ProofAudit.Audit

#audit axioms Parser.Provenance.Table.Extension.lookup
#audit axioms Parser.Provenance.Table.Extension.refl
#audit axioms Parser.Provenance.Table.Extension.trans
#audit axioms Parser.Provenance.Table.Extension.trans_ref
#audit axioms Parser.Provenance.Table.append_extension
#audit axioms Parser.Provenance.Table.appended_lookup
#audit axioms Parser.Provenance.TracesTo.extend
#audit axioms Parser.Provenance.Node.mapRule_parents
#audit axioms Parser.Provenance.Node.mapRule_source
#audit axioms Parser.Provenance.Table.unmap_mapRef
#audit axioms Parser.Provenance.Table.map_unmapRef
#audit axioms Parser.Provenance.Table.get_mapRef
#audit axioms Parser.Provenance.Table.get_unmapRef
#audit axioms Parser.Provenance.TracesTo.mapRule
#audit axioms Parser.Provenance.TracesTo.unmapRule
#audit axioms Parser.Provenance.Table.mapRule_traces_iff

#audit axioms RegularExpression.rmatch_iff_matches'
#audit axioms Parser.Source.Cursor.nextn_splits
#audit axioms Parser.Source.Cursor.find_splits
#audit axioms Parser.Source.Cursor.extract_between
#audit axioms Parser.Source.Spelled.space
#audit axioms Parser.Source.attach_complete
#audit axioms RegularExpression.simplify_correct
#audit axioms Parser.CertifiedDFA.run_correct
#audit axioms Parser.Alphabet.encode_reflects
#audit axioms Parser.LALR.Tree.prependWord_eq
#audit axioms Parser.LALR.Tree.valid_derives
#audit axioms Parser.LALR.checkTree_sound
#audit axioms Parser.LALR.parse_sound
#audit axioms Parser.LALR.run_more_fuel
#audit axioms Parser.LALR.Safety.validate_iff
#audit axioms Parser.LALR.Safety.path_state_lt
#audit axioms Parser.LALR.Safety.path_state_zero
#audit axioms Parser.LALR.Safety.Path.drop
#audit axioms Parser.LALR.Safety.pop_sound
#audit axioms Parser.LALR.Safety.reduction_pop
#audit axioms Parser.LALR.Safety.acceptance_stack
#audit axioms Parser.LALR.Safety.step_safe
#audit axioms Parser.LALR.Safety.run_safe
#audit axioms Parser.LALR.Safety.validated_run_safe
#audit axioms Parser.LALR.Safety.validated_parse_safe
#audit axioms Parser.LALR.RuntimeProofs.step_effect
#audit axioms Parser.LALR.RuntimeProofs.Effect.preserves
#audit axioms Parser.LALR.RuntimeProofs.Effect.accepts
#audit axioms Parser.LALR.RuntimeProofs.run_checked
#audit axioms Parser.LALR.FirstProofs.sequence_nullable
#audit axioms Parser.LALR.FirstProofs.sequence_begins
#audit axioms Parser.LALR.FirstProofs.nullable_append
#audit axioms Parser.LALR.FirstProofs.begins_append
#audit axioms Parser.LALR.FirstProofs.Below.append_right
#audit axioms Parser.LALR.FirstProofs.Below.cons
#audit axioms Parser.LALR.FirstProofs.validated_closed
#audit axioms Parser.LALR.FirstProofs.rewrites_below
#audit axioms Parser.LALR.FirstProofs.produces_below
#audit axioms Parser.LALR.FirstProofs.derives_below
#audit axioms Parser.LALR.FirstProofs.nullable_complete
#audit axioms Parser.LALR.FirstProofs.first_complete
#audit axioms Parser.LALR.FirstProofs.mem_lookaheads
#audit axioms Parser.LALR.FirstProofs.lookahead_complete
#audit axioms Parser.LALR.ItemCheck.validate_iff
#audit axioms Parser.LALR.ItemCheck.initial
#audit axioms Parser.LALR.ItemCheck.entry
#audit axioms Parser.LALR.ItemCheck.state_bound
#audit axioms Parser.LALR.ItemCheck.entry_at
#audit axioms Parser.LALR.ItemCheck.closure_lookahead
#audit axioms Parser.LALR.Execution.Steps.trans
#audit axioms Parser.LALR.Execution.Steps.run
#audit axioms Parser.LALR.Execution.action_row
#audit axioms Parser.LALR.Execution.shift
#audit axioms Parser.LALR.Execution.reduce
#audit axioms Parser.LALR.Execution.accept
#audit axioms Parser.LALR.Grammar.produces_valid
#audit axioms Parser.LALR.Grammar.derives_valid
#audit axioms Parser.LALR.Grammar.produces_forest
#audit axioms Parser.LALR.Grammar.derives_forest
#audit axioms Parser.LALR.Grammar.accepts_tree
#audit axioms Parser.LALR.Completeness.forest_derives
#audit axioms Parser.LALR.Completeness.word_valid
#audit axioms Parser.LALR.Completeness.tree_runs
#audit axioms Parser.LALR.Completeness.parse_tree
#audit axioms Parser.LALR.Completeness.parse_complete
#audit axioms Parser.LALR.Completeness.accepts_iff_parse
#audit axioms Parser.LALR.Fuel.validate_iff
#audit axioms Parser.LALR.Fuel.tree_bound
#audit axioms Parser.LALR.Fuel.sufficient
#audit axioms Parser.LALR.parse_more_fuel
#audit axioms Parser.LALR.Fuel.parse_complete
#audit axioms Parser.LALR.Fuel.accepts_iff_parse
#audit axioms Parser.LALR.Progress.validate_iff
#audit axioms Parser.LALR.Progress.vertex_bound
#audit axioms Parser.LALR.Progress.path_weight
#audit axioms Parser.LALR.Progress.potential_nonnegative
#audit axioms Parser.LALR.Progress.effect_decreases
#audit axioms Parser.LALR.Progress.run_not_exhausted
#audit axioms Parser.LALR.Progress.initial_not_exhausted
#audit axioms Parser.LALR.parse_eq_run
#audit axioms Parser.LALR.run_more_completed
#audit axioms Parser.LALR.Progress.parse_not_exhausted
#audit axioms Parser.LALR.Progress.parse_terminates
#audit axioms Parser.LALR.Progress.accepts_iff_parse
#audit axioms Parser.Scanner.symbol_correct
#audit axioms Parser.Scanner.lex_correct
#audit axioms Parser.Scanner.SymbolLexes.single_unpaired
#audit axioms Parser.Scanner.pairMatches_iff
#audit axioms Parser.Scanner.readSymbol_disjoint
#audit axioms Parser.Scanner.scan_disjoint
#audit axioms Parser.Scanner.lex_disjoint
#audit axioms Parser.Source.Span.bounded
#audit axioms Parser.Source.Span.cover_left
#audit axioms Parser.Source.Span.cover_right
#audit axioms Parser.Source.Aligned.erases
#audit axioms Parser.Source.Aligned.lexemes
#audit axioms Parser.Source.Aligned.disjoint
#audit axioms Parser.Source.attachLoop_eq_reference
#audit axioms Parser.Source.attach_eq_reference
#audit axioms Parser.Source.lexLocated_eq_reference
#audit axioms Parser.LALR.decorate_erases
#audit axioms Parser.LALR.decorate_wellSpanned
#audit axioms Parser.LALR.LocatedTree.empty_span
#audit axioms Parser.LALR.LocatedParse.sound
#audit axioms Parser.Parallel.map_eq
#audit axioms Parser.Scanner.Lexes.spelled
#audit axioms Parser.Scanner.lex_locations
#audit axioms Parser.Provenance.Table.get_lift
#audit axioms Parser.Provenance.Table.get_last
#audit axioms Parser.Provenance.Table.source_lookup
#audit axioms Parser.Provenance.Table.derived_lookup
#audit axioms Parser.Provenance.Table.generated_lookup
#audit axioms Parser.Provenance.traces_source
#audit axioms Parser.Provenance.TracesTo.lift
#audit axioms Parser.Provenance.TracesTo.derive
#audit axioms Parser.Provenance.TracesTo.generate
