import GALECParser.StructureBridge
import GALECParser.ActionCoverage
import GALECParser.ProfileProjection

/-! Actions consume the actual accepted CST once. The source entrypoint owns
parser diagnostics; no token decoder, reconstruction or second parse executes. -/
namespace Rumoca.GALEC.Structural
open _root_.Parser LALR LALR.Frontend

def build (tree : Tree) (tokens : List Token) : Option AST.Block :=
  (StructureBridge.build tree tokens).bind
    (StructuralActions.run rules Token.symbol (.ref "program"))

def buildScalar (tree : Tree) (tokens : List Token) : Option Syntax.Block :=
  (build tree tokens).bind ProfileProjection.toScalar

def buildTensor (tree : Tree) (tokens : List Token) : Option Syntax.TensorBlock :=
  (build tree tokens).bind ProfileProjection.toTensor

theorem build_iff (tree : Tree) (tokens : List Token) (ast : AST.Block) :
    build tree tokens = some ast ↔ ∃ v, StructureBridge.build tree tokens = some v ∧
      StructuralActions.Denotes rules Token.symbol (.ref "program") v ast := by
  simp only [build, Option.bind_eq_some_iff]
  apply exists_congr
  intro v
  exact and_congr_right fun _ => program_correct v ast

theorem build_total (parsed : StructureBridge.parser.run tokens = .ok tree) :
    ∃ ast, build tree tokens = some ast := by
  obtain ⟨v, built, root⟩ := StructureBridge.build_total parsed
  obtain ⟨valid, shape⟩ := StructureBridge.root_valid parsed root
  obtain ⟨ast, denotes⟩ := program_total valid shape
  exact ⟨ast, (build_iff tree tokens ast).mpr ⟨v, built, denotes⟩⟩

theorem build_sound (parsed : StructureBridge.parser.run tokens = .ok tree)
    (success : build tree tokens = some ast) :
    ∃ v, Structure.Root Generated.sourceGrammar Generated.grammar.start
        StructureBridge.decode StructureBridge.parser.encode Generated.runtimeRules tree tokens v ∧
      StructuralActions.Denotes rules Token.symbol (.ref "program") v ast ∧
      v.tokens = tokens ∧ Structure.Valid Generated.sourceGrammar Token.symbol v ∧
      v.expr = .ref "program" := by
  obtain ⟨v, built, denotes⟩ := (build_iff tree tokens ast).mp success
  have root := StructureBridge.build_sound parsed built
  obtain ⟨valid, shape⟩ := StructureBridge.root_valid parsed root
  have yield : v.tokens = tokens := by
    simpa only [Structure.Value.prependTokens_eq, List.append_nil] using root.1
  exact ⟨v, root, denotes, yield, valid, shape⟩

end Rumoca.GALEC.Structural
