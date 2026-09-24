import GALECParser.StructureBridge
import GALECParser.ActionCoverage

/-! Actions consume the actual accepted CST once. The source entrypoint owns
parser diagnostics; no token decoder, reconstruction or second parse executes.
This is syntax only: no name, index, range, shape or mutation checking. -/
namespace Rumoca.GALEC.Structural
open _root_.Parser LALR LALR.Frontend

def build (tree : Tree) (tokens : List Token) : Option AST.Block :=
  (StructureBridge.build tree tokens).bind
    (StructuralActions.run rules Token.symbol (.ref "block"))

theorem build_iff (tree : Tree) (tokens : List Token) (ast : AST.Block) :
    build tree tokens = some ast ↔ ∃ v, StructureBridge.build tree tokens = some v ∧
      StructuralActions.Denotes rules Token.symbol (.ref "block") v ast := by
  simp only [build, Option.bind_eq_some_iff]
  apply exists_congr
  intro v
  exact and_congr_right fun _ => block_correct v ast

theorem build_total (parsed : StructureBridge.parser.run tokens = .ok tree) :
    ∃ ast, build tree tokens = some ast := by
  obtain ⟨v, built, root⟩ := StructureBridge.build_total parsed
  obtain ⟨valid, shape⟩ := StructureBridge.root_valid parsed root
  obtain ⟨ast, denotes⟩ := block_total valid shape
  exact ⟨ast, (build_iff tree tokens ast).mpr ⟨v, built, denotes⟩⟩

theorem build_sound (parsed : StructureBridge.parser.run tokens = .ok tree)
    (success : build tree tokens = some ast) :
    ∃ v, Structure.Root Generated.sourceGrammar Generated.grammar.start
        StructureBridge.decode StructureBridge.parser.encode Generated.runtimeRules tree tokens v ∧
      StructuralActions.Denotes rules Token.symbol (.ref "block") v ast ∧
      v.tokens = tokens ∧ Structure.Valid Generated.sourceGrammar Token.symbol v ∧
      v.expr = .ref "block" := by
  obtain ⟨v, built, denotes⟩ := (build_iff tree tokens ast).mp success
  have root := StructureBridge.build_sound parsed built
  obtain ⟨valid, shape⟩ := StructureBridge.root_valid parsed root
  have yield : v.tokens = tokens := by
    simpa only [Structure.Value.prependTokens_eq, List.append_nil] using root.1
  exact ⟨v, root, denotes, yield, valid, shape⟩

/-- The table parser produces the only CST consumed by `build`. -/
def parse (tokens : List Token) : Option AST.Block :=
  match StructureBridge.parser.run tokens with
  | .error _ => none
  | .ok tree => build tree tokens

theorem parse_iff (tokens : List Token) (ast : AST.Block) :
    parse tokens = some ast ↔ ∃ tree v,
      StructureBridge.parser.run tokens = .ok tree ∧
      StructureBridge.build tree tokens = some v ∧
      StructuralActions.Denotes rules Token.symbol (.ref "block") v ast := by
  unfold parse
  split
  · rename_i failure failed
    simp [failed]
  · rename_i tree parsed
    simp only [parsed, Except.ok.injEq, exists_and_left, exists_eq_left']
    exact build_iff tree tokens ast

/-- All token streams, not merely renderer images or selected examples. -/
theorem accepts_iff (tokens : List Token) :
    (∃ ast, parse tokens = some ast) ↔
      EBNF.Accepts Generated.sourceGrammar (tokens.map Token.symbol) := by
  constructor
  · rintro ⟨ast, success⟩
    obtain ⟨tree, v, parsed, built, _⟩ := (parse_iff tokens ast).mp success
    apply (StructureBridge.source_accepts_iff tokens).mp
    exact ⟨v, (StructureBridge.parse_eq_build parsed).trans built⟩
  · intro accepted
    obtain ⟨v, success⟩ := (StructureBridge.source_accepts_iff tokens).mpr accepted
    obtain ⟨tree, parsed, _⟩ := StructureBridge.sound tokens v success
    obtain ⟨ast, built⟩ := build_total parsed
    exact ⟨ast, by simp only [parse, parsed]; exact built⟩

end Rumoca.GALEC.Structural
