import ModelicaParser.GeneratedRuntime
import ModelicaParser.AST

open _root_.Parser

namespace Rumoca

def parseTokens (ts : List Token) : Option AST.Model :=
  if RuntimeGenerated.recognize (ts.map (RuntimeGenerated.encode ∘ Token.symbol)) then AST.decode ts else none

theorem parseTokens_sound (ts : List Token) (m : AST.Model) (h : parseTokens ts = some m) :
    ts = m.tokens := by
  unfold parseTokens at h
  split at h
  · exact AST.decode_sound ts m h
  · contradiction

def tokenPattern : List RuntimeGenerated.Letter :=
  (AST.Model.mk "" "" "" "").tokens.map (RuntimeGenerated.encode ∘ Token.symbol)

theorem tokens_encode (m : AST.Model) :
    m.tokens.map (RuntimeGenerated.encode ∘ Token.symbol) = tokenPattern := rfl

set_option maxRecDepth 10000 in
theorem pattern_checked : RuntimeGenerated.recognize tokenPattern = true := by decide +kernel

theorem parseTokens_complete (m : AST.Model) : parseTokens m.tokens = some m := by
  simp only [parseTokens, tokens_encode, pattern_checked, ↓reduceIte, AST.decode_complete]

theorem parseTokens_iff (ts : List Token) (m : AST.Model) :
    parseTokens ts = some m ↔ ts = m.tokens :=
  ⟨fun h => parseTokens_sound ts m h, fun h => h ▸ parseTokens_complete m⟩

/-- Proofs bind syntax to the exact input; they are erased from execution. -/
structure Parsed (source : String) where
  tokens : List Token
  ast : AST.Model
  lexical : lex source = .ok tokens
  syntactic : parseTokens tokens = some ast

def parse (source : String) : Except Diagnostic (Parsed source) :=
  match hl : lex source with
  | .error e => .error e
  | .ok ts =>
    match hp : parseTokens ts with
    | none => .error ⟨"parse", 0,
        "expected: model NAME Real STATE; equation der(STATE) = 1; end NAME;"⟩
    | some ast => .ok ⟨ts, ast, hl, hp⟩

theorem parsed_source (p : Parsed source) : lex source = .ok p.ast.tokens := by
  rw [p.lexical, parseTokens_sound p.tokens p.ast p.syntactic]

/-- Soundness reaches the characters of the input file, not just token codes. -/
theorem parsed_lexes (p : Parsed source) : Lexes source.toList p.ast.tokens :=
  (lex_correct source _).mp (parsed_source p)

/-- Every source admitted by the lexical and AST specification has a certified
parse; no grammar-valid model of this tiny profile is excluded. -/
def parsedOfSyntax (source : String) (m : AST.Model) (h : Lexes source.toList m.tokens) :
    Parsed source := ⟨m.tokens, m, (lex_correct source _).mpr h, parseTokens_complete m⟩

theorem parse_complete (source : String) (m : AST.Model) (h : Lexes source.toList m.tokens) :
    ∃ p, parse source = .ok p ∧ p.ast = m := by
  unfold parse
  have hl := (lex_correct source _).mpr h
  split
  · rename_i e he
    simp [he] at hl
  · rename_i ts ht
    have heq : ts = m.tokens := Except.ok.inj (ht.symm.trans hl)
    subst ts
    split
    · rename_i hn
      simp [parseTokens_complete] at hn
    · rename_i ast ha
      have heq : ast = m := Option.some.inj (ha.symm.trans (parseTokens_complete m))
      subst ast
      exact ⟨_, rfl, rfl⟩

/-- A source-bound certificate describes the actual executable parser result. -/
theorem parse_eq_parsed (p : Parsed source) : parse source = .ok p := by
  obtain ⟨q, hq, ha⟩ := parse_complete source p.ast (parsed_lexes p)
  have ht : q.tokens = p.tokens := Except.ok.inj (q.lexical.symm.trans p.lexical)
  cases p with
  | mk pt pa pl ps =>
    cases q with
    | mk qt qa ql qs =>
      dsimp at ha ht
      subst qa
      subst qt
      exact hq

end Rumoca
