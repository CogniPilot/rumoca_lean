import GALECParser.Syntax
import GALECParser.Generated
import Parser.LALR.Soundness

open _root_.Parser

namespace Rumoca.GALEC.Syntax

def encode (token : Token) : Nat := Generated.encode token.symbol

def parseTree (tokens : List Token) : Except LALR.Failure LALR.Tree :=
  Generated.parseSymbols (tokens.map Token.symbol)

theorem in_grammar (b : Block) :
    EBNF.Accepts Generated.sourceGrammar (b.tokens.map Token.symbol) := by
  simp [Generated.start_rule, Generated.rule_block, Generated.rule_startup,
    Generated.rule_recalibrate, Generated.rule_do_step, Generated.rule_reference,
    EBNF.Derives.seq_iff, EBNF.Derives.terminal_iff, Block.tokens, Token.symbol]

theorem tree_complete (b : Block) : ∃ tree, parseTree b.tokens = .ok tree :=
  (Generated.source_parse_correct _).2.1.mp (in_grammar b)

private theorem tree_language (parsed : parseTree tokens = .ok tree) :
    Generated.grammar.Accepts (tokens.map encode) := by
  have accepted := (Generated.parse_correct
    ((tokens.map Token.symbol).map Generated.encode)).1.mpr ⟨tree, parsed⟩
  simpa only [List.map_map, Function.comp_def, encode] using accepted

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
            tokens_of_decode ha ▸ tree_language ht, hr⟩
        else .error ⟨"GALEC resolve", 0, "mismatched block/state/clock name"⟩

theorem parse_complete (source : String) (b : Block)
    (lexical : Scanner.Lexes scanner source.toList b.tokens) (resolved : Resolved b) :
    ∃ p : Parsed source, parse source = .ok p ∧ p.ast = b := by
  obtain ⟨tree, ht⟩ := tree_complete b
  have hl := (Scanner.lex_correct scanner source b.tokens).mpr lexical
  refine ⟨⟨b, lexical, tree_language ht, resolved⟩, ?_, rfl⟩
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
