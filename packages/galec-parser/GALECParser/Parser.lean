import GALECParser.Syntax
import GALECParser.Generated
import Parser.LALR.Soundness

open _root_.Parser

namespace Rumoca.GALEC.Syntax

def encode (token : Token) : Nat :=
  (Generated.alphabet.findIdx? (· == token.symbol)).getD (Generated.alphabet.size + 1)

def parseTree (tokens : List Token) : Except LALR.Failure LALR.Tree :=
  LALR.parse Generated.grammar Generated.tables (8 * (tokens.length + 1)) (tokens.map encode)

structure Parsed (source : String) where
  ast : Block
  lexical : Scanner.Lexes scanner source.toList ast.tokens
  grammar : Generated.grammar.Accepts (ast.tokens.map encode)
  resolved : Resolved ast

def parse (source : String) : Except Diagnostic (Parsed source) :=
  match hl : Scanner.lex scanner source with
  | .error e => .error e
  | .ok tokens => match ht : parseTree tokens with
    | .error _ => .error ⟨"GALEC syntax", 0, "outside the certified unit grammar profile"⟩
    | .ok _tree => match ha : decode tokens with
      | none => .error ⟨"GALEC action", 0, "outside the unit action profile"⟩
      | some ast =>
        if hr : Resolved ast then
          .ok ⟨ast, tokens_of_decode ha ▸ (Scanner.lex_correct scanner source tokens).mp hl,
            tokens_of_decode ha ▸ (LALR.parse_sound _ _ _ _ _ ht).2.2, hr⟩
        else .error ⟨"GALEC resolve", 0, "mismatched block/state/clock name"⟩

theorem encoded_tokens (b : Block) : b.tokens.map encode = unit.tokens.map encode := rfl
theorem token_count (b : Block) : b.tokens.length = unit.tokens.length := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem unit_tree_checked : (parseTree unit.tokens).isOk = true := by decide +kernel

/-- The actual shared LALR machine accepts every named instance of this token
profile. This is a profile-specific bound, not generic LR completeness. -/
theorem tree_complete (b : Block) : ∃ tree, parseTree b.tokens = .ok tree := by
  have h := unit_tree_checked
  have he : parseTree b.tokens = parseTree unit.tokens := by
    simp only [parseTree, encoded_tokens, token_count]
  rw [← he] at h
  cases ht : parseTree b.tokens with
  | error e => simp [ht, Except.isOk, Except.toBool] at h
  | ok tree => exact ⟨tree, rfl⟩

theorem parse_complete (source : String) (b : Block)
    (lexical : Scanner.Lexes scanner source.toList b.tokens) (resolved : Resolved b) :
    ∃ p : Parsed source, parse source = .ok p ∧ p.ast = b := by
  obtain ⟨tree, ht⟩ := tree_complete b
  have hl := (Scanner.lex_correct scanner source b.tokens).mpr lexical
  refine ⟨⟨b, lexical, (LALR.parse_sound _ _ _ _ _ ht).2.2, resolved⟩, ?_, rfl⟩
  unfold parse
  split
  · rename_i e he
    rw [hl] at he
    contradiction
  · rename_i tokens he
    have heq := Except.ok.inj (he.symm.trans hl)
    subst tokens
    split
    · rename_i e he
      rw [ht] at he
      contradiction
    · split
      · rename_i he
        rw [decode_tokens] at he
        contradiction
      · rename_i ast he
        have heq := Option.some.inj ((decode_tokens b).symm.trans he)
        subst ast
        simp only [dif_pos resolved]

end Rumoca.GALEC.Syntax
