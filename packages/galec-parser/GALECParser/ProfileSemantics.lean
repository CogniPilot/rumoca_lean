import GALECParser.ProfileWords
import GALECParser.ActionCoverage

/-! Direct profile semantics for arbitrary valid structural trees. This proof
chain uses only generic action semantics/totality and the concrete typed table;
there is no finite-engine comparison, old parser or decoder dependency. -/
namespace Rumoca.GALEC.Structural.ProfileSemantics
open _root_.Parser LALR.Frontend StructuralActions
open Structural

theorem scalar_denotes_yield {v : Structure.Value Token} {b : Syntax.Block}
    (h : StructuralActions.Denotes rules Token.symbol (.ref "program") v
      (ProfileProjection.ofScalar b)) : v.tokens = b.tokens :=
  scalar_words_yield b v.tokens (denotes_words h)

theorem tensor_denotes_yield {v : Structure.Value Token} {b : Syntax.TensorBlock}
    (h : StructuralActions.Denotes rules Token.symbol (.ref "program") v
      (ProfileProjection.ofTensor b)) : v.tokens = b.tokens :=
  tensor_words_yield b v.tokens (denotes_words h)

/-- Completeness for any valid structural realization with these payloads,
not a canonical tree reconstruction or a parse-tree uniqueness argument. -/
theorem scalar_denotes_of_yield {v : Structure.Value Token} {b : Syntax.Block}
    (valid : Structure.Valid Generated.sourceGrammar Token.symbol v)
    (shape : v.expr = .ref "program") (yield : v.tokens = b.tokens) :
    StructuralActions.Denotes rules Token.symbol (.ref "program") v
      (ProfileProjection.ofScalar b) := by
  obtain ⟨ast, h⟩ := program_total valid shape
  have words := denotes_words h
  rw [yield] at words
  have same := scalar_words_ast b ast words
  exact same ▸ h

theorem tensor_denotes_of_yield {v : Structure.Value Token} {b : Syntax.TensorBlock}
    (valid : Structure.Valid Generated.sourceGrammar Token.symbol v)
    (shape : v.expr = .ref "program") (yield : v.tokens = b.tokens) :
    StructuralActions.Denotes rules Token.symbol (.ref "program") v
      (ProfileProjection.ofTensor b) := by
  obtain ⟨ast, h⟩ := program_total valid shape
  have words := denotes_words h
  rw [yield] at words
  have same := tensor_words_ast b ast words
  exact same ▸ h

theorem scalar_denotes_iff {v : Structure.Value Token} {b : Syntax.Block}
    (valid : Structure.Valid Generated.sourceGrammar Token.symbol v)
    (shape : v.expr = .ref "program") :
    StructuralActions.Denotes rules Token.symbol (.ref "program") v
      (ProfileProjection.ofScalar b) ↔ v.tokens = b.tokens :=
  ⟨scalar_denotes_yield, scalar_denotes_of_yield valid shape⟩

theorem tensor_denotes_iff {v : Structure.Value Token} {b : Syntax.TensorBlock}
    (valid : Structure.Valid Generated.sourceGrammar Token.symbol v)
    (shape : v.expr = .ref "program") :
    StructuralActions.Denotes rules Token.symbol (.ref "program") v
      (ProfileProjection.ofTensor b) ↔ v.tokens = b.tokens :=
  ⟨tensor_denotes_yield, tensor_denotes_of_yield valid shape⟩

end Rumoca.GALEC.Structural.ProfileSemantics

