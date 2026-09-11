import Parser
import Parser.LALR.FirstProofs
import Parser.LALR.RuntimeProofs
import Parser.LALR.SafetyProofs
import Parser.Automaton
import Parser.Alphabet
import Parser.ScannerRefinement
import Parser.LocatedProofs
import ProofAudit.Audit

#audit axioms RegularExpression.rmatch_iff_matches'
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
