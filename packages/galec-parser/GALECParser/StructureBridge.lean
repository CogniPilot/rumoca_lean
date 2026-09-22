import GALECParser.Generated
import Parser.LALR.EBNFStructure
import Parser.LALR.EBNFEncoding

/-! GALEC structural-parser boundary. Independent of the source entrypoint;
original tokens remain the payload. -/
namespace Rumoca.GALEC.StructureBridge
open _root_.Parser LALR LALR.Frontend

def parser : TokenParser Token := Generated.tokenParser.contramap Token.symbol

def decode (code : Nat) : Parser.Symbol := Generated.alphabet[code]?.getD .ident

def parse (tokens : List Token) : Option (Structure.Value Token) :=
  Structure.parse parser decode Generated.runtimeRules tokens


theorem total (tokens : List Token) (tree : Tree)
    (parsed : parser.run tokens = .ok tree) :
    ∃ value, parse tokens = some value ∧
      Structure.Root Generated.sourceGrammar Generated.grammar.start decode parser.encode
        Generated.runtimeRules tree tokens value := by
  exact Structure.parse_total parser Generated.prepared decode Generated.runtimeRules
    rfl rfl Generated.runtimeRules_eq (Witness.validate_iff.mp Generated.lowering_checked) parsed

theorem sound (tokens : List Token) (value : Structure.Value Token)
    (success : parse tokens = some value) :
    ∃ tree, parser.run tokens = .ok tree ∧
      Structure.Root Generated.sourceGrammar Generated.grammar.start decode parser.encode
        Generated.runtimeRules tree tokens value := by
  exact Structure.parse_sound parser Generated.prepared decode Generated.runtimeRules
    rfl rfl Generated.runtimeRules_eq (Witness.validate_iff.mp Generated.lowering_checked) success

theorem source_accepts_iff (tokens : List Token) :
    (∃ value, parse tokens = some value) ↔
      EBNF.Accepts Generated.sourceGrammar (tokens.map Token.symbol) := by
  unfold parse
  rw [Structure.parse_accepts_iff parser Generated.prepared decode Generated.runtimeRules
    rfl rfl Generated.runtimeRules_eq (Witness.validate_iff.mp Generated.lowering_checked)]
  simpa only [parser, TokenParser.contramap, Generated.tokenParser, List.map_map]
    using (Generated.ebnf_correct (tokens.map Token.symbol)).symm

set_option maxRecDepth 10000 in
theorem classifier_compatible (tokens : List Token) (tree : Tree)
    (parsed : parser.run tokens = .ok tree) :
    tokens.map (decode ∘ parser.encode) = tokens.map Token.symbol := by
  have accepted := (parser.accepts_iff tokens).mpr ⟨tree, parsed⟩
  have valid := accepted_tokens_valid (g := Generated.grammar) (by decide +kernel) accepted
  apply List.map_congr_left
  intro token member
  apply Prepared.decode_encode (p := Generated.prepared)
  have bounded := valid (parser.encode token) (List.mem_map.mpr ⟨token, member, rfl⟩)
  exact bounded

theorem syntax_sound (tokens : List Token) (value : Structure.Value Token)
    (success : parse tokens = some value) :
    value.prependTokens [] = tokens ∧
      EBNF.Derives Generated.sourceGrammar value.expr (tokens.map Token.symbol) := by
  obtain ⟨tree, parsed, recovered, _, name, _, _, _, expression, _, derives, _⟩ :=
    sound tokens value success
  refine ⟨recovered, ?_⟩
  rw [expression, ← classifier_compatible tokens tree parsed]
  exact derives

def build (tree : Tree) (tokens : List Token) : Option (Structure.Value Token) :=
  Structure.build decode parser.encode Generated.runtimeRules tree tokens

theorem parse_eq_build (parsed : parser.run tokens = .ok tree) :
    parse tokens = build tree tokens := by
  simp only [parse, Structure.parse, parsed, build]

theorem build_total (parsed : parser.run tokens = .ok tree) :
    ∃ v, build tree tokens = some v ∧
      Structure.Root Generated.sourceGrammar Generated.grammar.start decode parser.encode
        Generated.runtimeRules tree tokens v := by
  simpa only [parse_eq_build parsed] using total tokens tree parsed

theorem build_sound (parsed : parser.run tokens = .ok tree)
    (success : build tree tokens = some v) :
    Structure.Root Generated.sourceGrammar Generated.grammar.start decode parser.encode
      Generated.runtimeRules tree tokens v := by
  obtain ⟨value, built, root⟩ := build_total parsed
  cases Option.some.inj (built.symm.trans success)
  exact root

/-- The independent token classifier validates the actual retained structure. -/
theorem root_valid (parsed : parser.run tokens = .ok tree)
    (root : Structure.Root Generated.sourceGrammar Generated.grammar.start decode parser.encode
      Generated.runtimeRules tree tokens v) :
    Structure.Valid Generated.sourceGrammar Token.symbol v ∧ v.expr = .ref "program" := by
  obtain ⟨recovered, _, name, body, tail, source, shape, valid, _, _⟩ := root
  have nameEq : name = "program" := by
    have heads := congrArg List.head? source
    simpa [Generated.sourceGrammar] using (congrArg (Option.map Prod.fst) heads).symm
  subst name
  refine ⟨valid.congr ?_, shape⟩
  have payloads : v.tokens = tokens := by
    simpa only [Structure.Value.prependTokens_eq, List.append_nil] using recovered
  have mapping := classifier_compatible tokens tree parsed
  rw [← payloads] at mapping
  exact List.map_inj_left.mp mapping

end Rumoca.GALEC.StructureBridge
