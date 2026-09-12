import ModelicaParser.Generated
import ModelicaParser.Lexer

open _root_.Parser

/-! A reusable contract for semantic actions over the certified token grammar.
Recognition and AST construction are separate: an action may select a smaller
syntactic profile, while soundness still binds its AST to the original text. -/
namespace Rumoca.ParserActions

/-- The same generated LR parser consumes every Modelica token profile. -/
def tokenParser : LALR.TokenParser Token :=
  Generated.tokenParser.contramap Token.symbol

/-- This frontend's exact-token AST relation. The reusable LR action API also
supports CST-dependent builders and more general source-to-AST relations. -/
structure Actions (α : Type) where
  tokens : α → List Token
  decode : List Token → Option α
  decode_sound : ∀ ts a, decode ts = some a → ts = tokens a
  decode_complete : ∀ a, decode (tokens a) = some a
  in_grammar : ∀ a, EBNF.Accepts Generated.sourceGrammar ((tokens a).map Token.symbol)

def Actions.lalr (actions : Actions α) : tokenParser.Actions α where
  Denotes ts ast := ts = actions.tokens ast
  build _tree ts := actions.decode ts
  language ts ast denotes := by
    subst ts
    simpa only [tokenParser, LALR.TokenParser.contramap, List.map_map] using
      (Generated.ebnf_correct _).mp (actions.in_grammar ast)
  sound _tree ts ast _checked decoded := actions.decode_sound ts ast decoded
  complete _tree ts ast _checked denotes := by
    subst ts
    exact actions.decode_complete ast

variable (actions : Actions α)

def parseTokens (ts : List Token) : Option α :=
  tokenParser.parseWith actions.lalr ts

theorem parseTokens_sound (h : parseTokens actions ts = some a) : ts = actions.tokens a :=
  tokenParser.parseWith_sound actions.lalr h

theorem parseTokens_complete (a : α) : parseTokens actions (actions.tokens a) = some a :=
  tokenParser.parseWith_complete actions.lalr rfl

structure Parsed (source : String) where
  tokens : List Token
  ast : α
  lexical : lex source = .ok tokens
  syntactic : parseTokens actions tokens = some ast

def parse (source : String) : Except Diagnostic (Parsed actions source) :=
  match hl : lex source with
  | .error e => .error e
  | .ok ts => match hp : parseTokens actions ts with
    | none => .error ⟨"parse", 0, "source is outside the selected grammar profile"⟩
    | some ast => .ok ⟨ts, ast, hl, hp⟩

theorem parsed_lexes (p : Parsed actions source) :
    Lexes source.toList (actions.tokens p.ast) := by
  apply (lex_correct _ _).mp
  rw [p.lexical, parseTokens_sound actions p.syntactic]

theorem parse_complete (source : String) (a : α)
    (h : Lexes source.toList (actions.tokens a)) :
    ∃ p, parse actions source = .ok p ∧ p.ast = a := by
  unfold parse
  have hl := (lex_correct source _).mpr h
  split
  · rename_i e he
    simp [he] at hl
  · rename_i ts ht
    have heq : ts = actions.tokens a := Except.ok.inj (ht.symm.trans hl)
    subst ts
    split
    · rename_i hn
      simp [parseTokens_complete] at hn
    · rename_i ast ha
      have heq : ast = a := Option.some.inj (ha.symm.trans (parseTokens_complete actions a))
      subst ast
      exact ⟨_, rfl, rfl⟩

theorem parse_eq_parsed (p : Parsed actions source) : parse actions source = .ok p := by
  obtain ⟨q, hq, ha⟩ := parse_complete actions source p.ast (parsed_lexes actions p)
  have ht : q.tokens = p.tokens := Except.ok.inj (q.lexical.symm.trans p.lexical)
  cases p with
  | mk pt pa pl ps =>
    cases q with
    | mk qt qa ql qs =>
      dsimp at ha ht
      subst qa
      subst qt
      exact hq

end Rumoca.ParserActions
