import ModelicaParser.GeneratedRuntime
import ModelicaParser.Lexer

open _root_.Parser

/-! A reusable contract for semantic actions over the certified token grammar.
Recognition and AST construction are separate: an action may select a smaller
syntactic profile, while soundness still binds its AST to the original text. -/
namespace Rumoca.ParserActions

structure Actions (α : Type) where
  tokens : α → List Token
  decode : List Token → Option α
  decode_sound : ∀ ts a, decode ts = some a → ts = tokens a
  decode_complete : ∀ a, decode (tokens a) = some a
  recognized : ∀ a, RuntimeGenerated.recognize
    ((tokens a).map (RuntimeGenerated.encode ∘ Token.symbol)) = true

variable (actions : Actions α)

def parseTokens (ts : List Token) : Option α :=
  if RuntimeGenerated.recognize (ts.map (RuntimeGenerated.encode ∘ Token.symbol))
    then actions.decode ts else none

theorem parseTokens_sound (h : parseTokens actions ts = some a) : ts = actions.tokens a := by
  unfold parseTokens at h
  split at h
  · exact actions.decode_sound _ _ h
  · contradiction

theorem parseTokens_complete (a : α) : parseTokens actions (actions.tokens a) = some a := by
  simp only [parseTokens, actions.recognized, if_true, actions.decode_complete]

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
