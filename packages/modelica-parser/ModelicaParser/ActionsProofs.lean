import ModelicaParser.Actions
import ModelicaParser.ParserProofs

open _root_.Parser

namespace Rumoca.ParserActions

/-- Any action implementation satisfying the public contract inherits the
certified EBNF language result over original, uncompressed token symbols. -/
theorem parsed_in_ebnf (p : Parsed actions source) :
    Generated.rawGrammar.Accepts (p.tokens.map Token.symbol) := by
  have h := p.syntactic
  unfold parseTokens at h
  split at h
  · exact (runtime_symbols_correct _).mp (by simpa only [List.map_map] using ‹_ = true›)
  · contradiction

end Rumoca.ParserActions
