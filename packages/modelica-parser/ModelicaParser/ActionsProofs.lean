import ModelicaParser.Actions

open _root_.Parser

namespace Rumoca.ParserActions

/-- Every frontend action contract inherits the shared EBNF/LALR guarantee. -/
theorem parsed_in_ebnf (p : Parsed actions source) :
    EBNF.Accepts Generated.sourceGrammar (p.tokens.map Token.symbol) := by
  apply (Generated.ebnf_correct _).mpr
  simpa only [tokenParser, LALR.TokenParser.contramap, List.map_map] using
    tokenParser.parseWith_grammar actions.lalr p.syntactic

end Rumoca.ParserActions
