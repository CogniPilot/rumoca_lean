import ProofAudit.Audit
import Parser.LALR.FirstProofs
import Parser.LALR.Generator

/-! Kernel regressions for the independent nullable/FIRST certificate. The cbv
normalizer constructs proof terms; it does not use native-reduction axioms. -/
set_option cbv.warning false

namespace Parser.LRFirstChecks
open LALR

/-- S → A B; A → ε | a A; B → b. -/
def grammar : Grammar := ⟨2, 3, 0, #[
  ⟨0, [.nonterminal 1, .nonterminal 2]⟩,
  ⟨1, []⟩, ⟨1, [.terminal 0, .nonterminal 1]⟩,
  ⟨2, [.terminal 1]⟩]⟩

def facts : Array First := #[⟨false, [0, 1]⟩, ⟨true, [0]⟩, ⟨false, [1]⟩]

theorem certificate : FirstCheck.validate grammar facts = true := by cbv

theorem generator_solution : firstSets grammar = .ok facts := by cbv

theorem inherited_lookahead :
    lookaheads facts [.nonterminal 1] 2 = [0, 2] ∧
    lookaheads facts [.nonterminal 1, .nonterminal 2] 2 = [0, 1] := by
  constructor <;> cbv

theorem missing_nullable : FirstCheck.validate grammar
    (facts.setIfInBounds 1 ⟨false, [0]⟩) = false := by cbv

theorem missing_direct_terminal : FirstCheck.validate grammar
    (facts.setIfInBounds 2 ⟨false, []⟩) = false := by cbv

theorem missing_transitive_terminal : FirstCheck.validate grammar
    (facts.setIfInBounds 0 ⟨false, [1]⟩) = false := by cbv

theorem missing_fact : FirstCheck.validate grammar (facts.pop) = false := by cbv

theorem eof_is_not_a_first_terminal : FirstCheck.validate grammar
    (facts.setIfInBounds 0 ⟨false, [0, 1, 2]⟩) = false := by cbv

theorem invalid_grammar : FirstCheck.validate
    { grammar with productions := grammar.productions.push ⟨0, [.nonterminal 3]⟩ }
    facts = false := by cbv

/-- Conservative summaries need not be exact. In particular, a nullable mark
does not itself prove that the grammar generates the empty word. -/
theorem conservative_not_exact :
    FirstCheck.validate grammar (Array.replicate 3 ⟨true, [0, 1]⟩) = true ∧
    ¬ grammar.Accepts [] := by
  refine ⟨by cbv, ?_⟩
  intro h
  have hd : grammar.semantics.Derives [.nonterminal grammar.start] [] := h
  have hn := FirstProofs.nullable_complete certificate hd
  have hf : (firstSequence facts [.nonterminal grammar.start]).nullable = false := by cbv
  exact Bool.false_ne_true (hf.symm.trans hn)

#audit axioms certificate
#audit axioms generator_solution
#audit axioms inherited_lookahead
#audit axioms missing_nullable
#audit axioms missing_direct_terminal
#audit axioms missing_transitive_terminal
#audit axioms missing_fact
#audit axioms eof_is_not_a_first_terminal
#audit axioms invalid_grammar
#audit axioms conservative_not_exact

end Parser.LRFirstChecks
