import ModelicaParser.Parser
import Parser.Located
import Parser.LALR.Rejection

open _root_.Parser

/-! Located Modelica parse. Token locations are attached to the very same
lexemes the certified parse consumes, comments included; syntax consumers
choose which token ranges they expose. A syntax rejection is placed at the
token the certified parser could not accept, or at the end of the text. -/
namespace Rumoca.Modelica

/-- Located lexemes retain the source-level lexical guarantee. -/
theorem located_lex_sound (l : Parser.Source.Lexed Rumoca.lex source trivia) :
    Rumoca.Lexes source.toList (l.tokens.map (·.value)) :=
  (Rumoca.lex_correct source _).mp l.lexical

structure LocatedParsed (source : String) where
  parsed : Parsed source
  locations : List (Parser.Source.Located source Token)
  aligned : Parser.Source.Aligned modelicaSpace source.startPos parsed.lexemes locations

/-- The locations of the code tokens, in source order. -/
def codeLocations (locations : List (Parser.Source.Located source Token)) :
    List (Parser.Source.Located source Token) :=
  locations.filter fun token => !isComment token.value

theorem codeLocations_values (locations : List (Parser.Source.Located source Token)) :
    (codeLocations locations).map (·.value) = code (locations.map (·.value)) := by
  simp [codeLocations, code, List.filter_map, Function.comp_def]

/-- The range of one code token, or the end of the text past the last one. -/
def locatedSpan (source : String) (tokens : List (Parser.Source.Located source Token))
    (index : Nat) : Parser.Source.Span source :=
  ((codeLocations tokens)[index]?).map (·.span) |>.getD (.point source.endPos)

namespace LocatedParsed
variable {source : String}

/-- The range of one code token, or the end of the text past the last one. -/
def tokenSpan (p : LocatedParsed source) (index : Nat) : Parser.Source.Span source :=
  locatedSpan source p.locations index

theorem erases (p : LocatedParsed source) : parse source = .ok p.parsed :=
  parse_eq_parsed p.parsed

theorem lexemes (p : LocatedParsed source) :
    ∀ token ∈ p.locations, token.span.text = token.value.text := p.aligned.lexemes

theorem disjoint (p : LocatedParsed source) :
    p.locations.Pairwise (fun a b => a.span.stop ≤ b.span.start) := p.aligned.disjoint

theorem codeLocations_erase (p : LocatedParsed source) :
    (codeLocations p.locations).map (·.value) = p.parsed.tokens := by
  rw [codeLocations_values, p.aligned.erases]
  rfl

theorem tokenSpan_text (p : LocatedParsed source) (index : Nat) (token : Token)
    (h : p.parsed.tokens[index]? = some token) :
    (p.tokenSpan index).text = token.text := by
  have he := congrArg (fun ts : List Token => ts[index]?) p.codeLocations_erase
  dsimp only at he
  rw [List.getElem?_map, h] at he
  cases hx : (codeLocations p.locations)[index]? with
  | none => simp [hx] at he
  | some located =>
    have hv : located.value = token := by simpa [hx] using he
    have member : located ∈ p.locations :=
      List.mem_of_mem_filter (List.mem_of_getElem? hx)
    have ht := p.lexemes located member
    simpa [tokenSpan, locatedSpan, hx, hv] using ht

end LocatedParsed

/-- The number of tokens accepted before the certified parser rejected the
input. It locates a syntax diagnostic only. -/
def rejectedAt (tokens : List Token) : Nat :=
  let word := tokens.map (Generated.encode ∘ Token.symbol)
  tokens.length - LALR.unconsumed Generated.grammar Generated.tables (Generated.fuel word) ⟨[], word⟩

def parseLocated (source : String) :
    Except (Parser.Source.Diagnostic source) (LocatedParsed source) :=
  match Source.lexLocated lex source modelicaSpace with
  | .error e => .error e
  | .ok l =>
    match hp : Structural.parse (code (l.tokens.map (·.value))) with
    | none => .error ⟨"parse", locatedSpan source l.tokens
        (rejectedAt (code (l.tokens.map (·.value)))), "outside the certified Modelica grammar", []⟩
    | some ast => .ok ⟨⟨l.tokens.map (·.value), ast, l.lexical, hp⟩, l.tokens, l.aligned⟩

end Rumoca.Modelica
