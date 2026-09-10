import ModelicaParser.Parser
import ModelicaParser.Generated

open _root_.Parser

namespace Rumoca

/-- The light runtime tables and the certified grammar tables must agree
definitionally. Changing either copy without the other breaks this proof. -/
theorem runtime_agrees (xs : List RuntimeGenerated.Letter) :
    RuntimeGenerated.recognize xs = Generated.recognize xs := rfl

theorem runtime_recognize_correct (xs : List RuntimeGenerated.Letter) :
    RuntimeGenerated.recognize xs = true ↔ Generated.grammar.Accepts xs := by
  rw [runtime_agrees]
  exact Generated.recognize_correct xs

theorem parsed_in_generated_language (p : Parsed source) :
    Generated.grammar.Accepts (p.tokens.map (RuntimeGenerated.encode ∘ Token.symbol)) := by
  have h := p.syntactic
  unfold parseTokens at h
  split at h
  · exact (runtime_recognize_correct _).mp (by assumption)
  · contradiction

/-- The executable recognizer is correct over original token symbols,
including arbitrary unknown symbols, before alphabet compression. -/
theorem runtime_symbols_correct (xs : List Symbol) :
    RuntimeGenerated.recognize (xs.map RuntimeGenerated.encode) = true ↔
      Generated.rawGrammar.Accepts xs := Generated.recognize_symbols_correct xs

theorem parsed_in_ebnf (p : Parsed source) :
    Generated.rawGrammar.Accepts (p.tokens.map Token.symbol) := by
  have h := p.syntactic
  unfold parseTokens at h
  split at h
  · exact (runtime_symbols_correct _).mp (by simpa only [List.map_map] using ‹_ = true›)
  · contradiction

end Rumoca
