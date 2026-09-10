import RumocaEFMI.AlgorithmCode
import RumocaCore.GALEC.UnitProfile
import GALECParser.GrammarProofs
import GALECParser.Parser

open _root_.Parser

namespace Rumoca.EFMI

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem unit_lexical : Scanner.lex GALEC.Syntax.scanner unitSource =
    .ok GALEC.Syntax.unit.tokens := by rfl

theorem unit_parsed : ∃ parsed, GALEC.Syntax.parse unitSource = .ok parsed ∧
    parsed.ast = GALEC.Syntax.unit :=
  GALEC.Syntax.parse_complete _ _ (Scanner.lex_correct _ _ _ |>.mp unit_lexical)
    GALEC.Syntax.unit_resolved

/-- Actual source grammar processing is checked in Lean, independently of the
native table producer. The general metalanguage/desugaring theorem is still
open; this equality binds this concrete generated CFG to its EBNF bytes. -/
theorem grammar_processed :
    (LALR.Frontend.compile GALEC.Generated.source).map (·.grammar) =
      .ok GALEC.Generated.grammar := GALEC.Generated.grammar_processed

theorem render_parses (m : GALEC.Model source) :
    ∃ parsed, GALEC.Syntax.parse (renderAlgorithm m) = .ok parsed ∧
      parsed.ast = GALEC.Syntax.unit := by
  rw [emission_is_unit]
  exact unit_parsed

/-- Name-checked source denotes the admitted lifecycle block, including the
sampling-period initialization, rather than only its integer token shape. -/
def Denotes (parsed : GALEC.Syntax.Block) (block : GALEC.Block Rumoca.Tensor.scalar) : Prop :=
  GALEC.Syntax.Resolved parsed ∧ block = GALEC.unitBlock

theorem render_denotes (m : GALEC.Model source) :
    ∃ parsed, GALEC.Syntax.parse (renderAlgorithm m) = .ok parsed ∧ Denotes parsed.ast m.block := by
  obtain ⟨p, hp, _⟩ := render_parses m
  exact ⟨p, hp, p.resolved, m.profile⟩

end Rumoca.EFMI
