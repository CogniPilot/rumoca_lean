import ModelicaParser.Parser

open _root_.Parser

namespace Rumoca

/-- The source certificate reaches the actual LALR entry and its exact CST. -/
theorem parsed_tree (p : Parsed source) :
    ∃ tree, Generated.parseSymbols (p.tokens.map Token.symbol) = .ok tree ∧
      LALR.checkTree Generated.grammar
        ((p.tokens.map Token.symbol).map Generated.encode) tree = true := by
  obtain ⟨tree, parsed, checked, _⟩ :=
    ParserActions.tokenParser.parseWith_execution _ p.syntactic
  refine ⟨tree, parsed, ?_⟩
  simpa only [ParserActions.tokenParser, LALR.TokenParser.contramap,
    List.map_map] using checked

theorem parsed_in_generated_language (p : Parsed source) :
    Generated.grammar.Accepts ((p.tokens.map Token.symbol).map Generated.encode) := by
  obtain ⟨tree, parsed, _⟩ := parsed_tree p
  exact (Generated.parse_correct _).1.mpr ⟨tree, parsed⟩

/-- Source membership is the independent recursive EBNF relation, over original
symbols, composed with the very same parser used by the executable frontend. -/
theorem parsed_in_ebnf (p : Parsed source) :
    EBNF.Accepts Generated.sourceGrammar (p.tokens.map Token.symbol) :=
  (Generated.ebnf_correct _).mpr (parsed_in_generated_language p)

end Rumoca
