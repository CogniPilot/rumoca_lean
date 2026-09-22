import GALECParser.Syntax
import GALECParser.Generated
import Parser.LALR.Soundness
import GALECParser.ProfileBuild

open _root_.Parser

namespace Rumoca.GALEC.Syntax

def encode (token : Token) : Nat := Generated.encode token.symbol

def parseTree (tokens : List Token) : Except LALR.Failure LALR.Tree :=
  Generated.parseSymbols (tokens.map Token.symbol)

theorem in_grammar (b : Block) :
    EBNF.Accepts Generated.sourceGrammar (b.tokens.map Token.symbol) := by
  rw [Generated.start_rule, Generated.rule_program, EBNF.Derives.alt_iff]
  refine Or.inl ?_
  simp [Generated.rule_block, Generated.rule_startup,
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
    | .ok tree => match ha : Structural.buildScalar tree tokens with
      | none => .error ⟨"GALEC action", 0, "outside the unit action profile"⟩
      | some ast =>
        if hr : Resolved ast then
          .ok ⟨ast, ((Structural.buildScalar_tokens_iff ht ast).mp ha) ▸
              (Scanner.lex_correct scanner source tokens).mp hl,
            ((Structural.buildScalar_tokens_iff ht ast).mp ha) ▸ tree_language ht, hr⟩
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
    · rename_i tree parsed
      have hb := (Structural.buildScalar_tokens_iff parsed b).mpr rfl
      split
      · rename_i he
        rw [hb] at he
        contradiction
      · rename_i ast he
        have heq := Option.some.inj (hb.symm.trans he)
        subst ast
        simp only [dif_pos resolved]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem in_grammar_tensor (b : TensorBlock) :
    EBNF.Accepts Generated.sourceGrammar (b.tokens.map Token.symbol) := by
  rw [Generated.start_rule, Generated.rule_program, EBNF.Derives.alt_iff]
  refine Or.inr ?_
  simp [Generated.rule_tensor_block, Generated.rule_startup, Generated.rule_recalibrate,
    Generated.rule_tensor_do_step, Generated.rule_product, Generated.rule_reference,
    EBNF.Derives.seq_iff, EBNF.Derives.terminal_iff, TensorBlock.tokens, Token.symbol]

theorem tree_complete_tensor (b : TensorBlock) : ∃ tree, parseTree b.tokens = .ok tree :=
  (Generated.source_parse_correct _).2.1.mp (in_grammar_tensor b)

/-- Independently checked tensor parse. The lexical, grammar and resolution
certificates mirror the scalar `Parsed`, over the fixed-extent tensor scanner. -/
structure TensorParsed (source : String) where
  ast : TensorBlock
  lexical : Scanner.Lexes tensorScanner source.toList ast.tokens
  grammar : Generated.grammar.Accepts (ast.tokens.map encode)
  resolved : ResolvedTensor ast

def parseTensor (source : String) : Except Diagnostic (TensorParsed source) :=
  match hl : Scanner.lex tensorScanner source with
  | .error e => .error e
  | .ok tokens => match ht : parseTree tokens with
    | .error _ => .error ⟨"GALEC syntax", 0, "outside the certified tensor grammar profile"⟩
    | .ok tree => match ha : Structural.buildTensor tree tokens with
      | none => .error ⟨"GALEC action", 0, "outside the tensor square action profile"⟩
      | some ast =>
        if hr : ResolvedTensor ast then
          .ok ⟨ast, ((Structural.buildTensor_tokens_iff ht ast).mp ha) ▸
              (Scanner.lex_correct tensorScanner source tokens).mp hl,
            ((Structural.buildTensor_tokens_iff ht ast).mp ha) ▸ tree_language ht, hr⟩
        else .error ⟨"GALEC resolve", 0, "mismatched tensor block/state/input name"⟩

theorem parseTensor_complete (source : String) (b : TensorBlock)
    (lexical : Scanner.Lexes tensorScanner source.toList b.tokens) (resolved : ResolvedTensor b) :
    ∃ p : TensorParsed source, parseTensor source = .ok p ∧ p.ast = b := by
  obtain ⟨tree, ht⟩ := tree_complete_tensor b
  have hl := (Scanner.lex_correct tensorScanner source b.tokens).mpr lexical
  refine ⟨⟨b, lexical, tree_language ht, resolved⟩, ?_, rfl⟩
  unfold parseTensor
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
    · rename_i tree parsed
      have hb := (Structural.buildTensor_tokens_iff parsed b).mpr rfl
      split
      · rename_i he
        rw [hb] at he
        contradiction
      · rename_i ast he
        have heq := Option.some.inj (hb.symm.trans he)
        subst ast
        simp only [dif_pos resolved]

end Rumoca.GALEC.Syntax
