import ModelicaParser.Actions
import Parser.Located

/-! Source locations for any action profile. The shared lexer attachment
computes offsets; language actions only select token ranges. -/
namespace Rumoca.ParserActions

open _root_.Parser

structure LocatedParsed (actions : Actions α) (source : String) where
  parsed : Parsed actions source
  locations : List (Source.Located source Token)
  aligned : Source.Aligned modelicaSpace source.startPos parsed.tokens locations

namespace LocatedParsed

def tokenSpan (p : LocatedParsed actions source) (index : Nat) : Source.Span source :=
  (p.locations[index]?).map (·.span) |>.getD (.point source.endPos)

theorem erases (p : LocatedParsed actions source) : parse actions source = .ok p.parsed :=
  parse_eq_parsed actions p.parsed

theorem lexemes (p : LocatedParsed actions source) :
    ∀ token ∈ p.locations, token.span.text = token.value.text := p.aligned.lexemes

theorem disjoint (p : LocatedParsed actions source) :
    p.locations.Pairwise (fun a b => a.span.stop ≤ b.span.start) := p.aligned.disjoint

theorem tokenSpan_text (p : LocatedParsed actions source) (index : Nat) (token : Token)
    (h : p.parsed.tokens[index]? = some token) :
    (p.tokenSpan index).text = token.text := by
  have he := congrArg (fun ts : List Token => ts[index]?) p.aligned.erases
  dsimp only at he
  rw [List.getElem?_map, h] at he
  cases hx : p.locations[index]? with
  | none => simp [hx] at he
  | some located =>
    have hv : located.value = token := by simpa [hx] using he
    have ht := p.lexemes located (List.mem_of_getElem? hx)
    simpa [tokenSpan, hx, hv] using ht

end LocatedParsed

def parseLocated (actions : Actions α) (source : String) :
    Except (Source.Diagnostic source) (LocatedParsed actions source) :=
  match Source.lexLocated lex source modelicaSpace with
  | .error e => .error e
  | .ok l =>
    match hp : parseTokens actions (l.tokens.map (·.value)) with
    | none => .error ⟨"parse", .point source.startPos, "source is outside the selected grammar profile", []⟩
    | some ast => .ok ⟨⟨l.tokens.map (·.value), ast, l.lexical, hp⟩, l.tokens, l.aligned⟩

end Rumoca.ParserActions
