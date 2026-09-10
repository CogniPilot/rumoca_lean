import ModelicaParser.Parser
import Parser.Located

open _root_.Parser

/-! Located entry point for the existing Modelica profile. Semantic ASTs and
compiler certificates remain unchanged; the sidecar is tied to the very same
source and token sequence. AST clients choose which child ranges they expose. -/
namespace Rumoca

/-- Located tokens retain the existing source-level lexical guarantee. -/
theorem located_lex_sound (l : Parser.Source.Lexed Rumoca.lex source trivia) :
    Rumoca.Lexes source.toList (l.tokens.map (·.value)) :=
  (Rumoca.lex_correct source _).mp l.lexical


structure LocatedParsed (source : String) where
  parsed : Parsed source
  locations : List (Parser.Source.Located source Token)
  aligned : Parser.Source.Aligned modelicaSpace source.startPos parsed.tokens locations

namespace LocatedParsed
variable {source : String}

def tokenSpan (p : LocatedParsed source) (index : Nat) : Parser.Source.Span source :=
  (p.locations[index]?).map (·.span) |>.getD (.point source.endPos)

def modelSpan (p : LocatedParsed source) : Parser.Source.Span source :=
  (p.tokenSpan 0).cover (p.tokenSpan 15)

/-- Name agreement is still the compiler's resolver. Locations only enrich its
failure report; an end-name error takes the same priority as in AST.resolve. -/
def resolve (p : LocatedParsed source) :
    Except (Parser.Source.Diagnostic source) (PLift (AST.Resolved p.parsed.ast)) :=
  match AST.resolve p.parsed.ast with
  | .ok resolved => .ok resolved
  | .error e => .error ⟨e.phase,
      p.tokenSpan (if p.parsed.ast.endName = p.parsed.ast.name then 8 else 14), e.message,
      [if p.parsed.ast.endName = p.parsed.ast.name then
        ⟨p.tokenSpan 3, "state declared here"⟩
      else ⟨p.tokenSpan 1, "model declared here"⟩]⟩

theorem erases (p : LocatedParsed source) : Rumoca.parse source = .ok p.parsed :=
  parse_eq_parsed p.parsed

theorem lexemes (p : LocatedParsed source) :
    ∀ token ∈ p.locations, token.span.text = token.value.text := p.aligned.lexemes

theorem disjoint (p : LocatedParsed source) :
    p.locations.Pairwise (fun a b => a.span.stop ≤ b.span.start) := p.aligned.disjoint

end LocatedParsed

/-- First mismatching terminal in this fixed profile, or EOF for a missing
terminal. This is an error location, not error recovery or a second parser. -/
private def mismatch (source : String) : List (Parser.Source.Located source Token) →
    List Symbol → Parser.Source.Span source
  | [], _ => .point source.endPos
  | t :: _, [] => t.span
  | t :: ts, s :: ss => if t.value.symbol = s then mismatch source ts ss else t.span

def parseLocated (source : String) : Except (Parser.Source.Diagnostic source) (LocatedParsed source) :=
  match Source.lexLocated lex source modelicaSpace with
  | .error e => .error e
  | .ok l =>
    match hp : parseTokens (l.tokens.map (·.value)) with
    | none => .error ⟨"parse", mismatch source l.tokens
        ((AST.Model.mk "" "" "" "").tokens.map Token.symbol),
        "expected: model NAME Real STATE; equation der(STATE) = 1; end NAME;", []⟩
    | some ast => .ok ⟨⟨l.tokens.map (·.value), ast, l.lexical, hp⟩, l.tokens, l.aligned⟩

end Rumoca
