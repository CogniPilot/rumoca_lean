import GALECParser.StructuralParser
import GALECParser.ProfileSemantics

/-! Checked profile projection of the actual accepted CST. Legacy decoder names
appear only in compatibility theorems, never in the executable builder. -/
namespace Rumoca.GALEC.Structural
open _root_.Parser LALR LALR.Frontend

theorem buildScalar_tokens_iff (parsed : StructureBridge.parser.run tokens = .ok tree)
    (b : Syntax.Block) : buildScalar tree tokens = some b ↔ tokens = b.tokens := by
  constructor
  · intro success
    obtain ⟨ast, built, projected⟩ := Option.bind_eq_some_iff.mp success
    have same := ProfileProjection.scalar_projection_exact projected
    subst ast
    obtain ⟨v, _, denotes, yield, valid, shape⟩ := build_sound parsed built
    exact yield.symm.trans ((ProfileSemantics.scalar_denotes_iff valid shape).mp denotes)
  · intro yield
    obtain ⟨v, structural, root⟩ := StructureBridge.build_total parsed
    obtain ⟨valid, shape⟩ := StructureBridge.root_valid parsed root
    have recovered : v.tokens = tokens := by
      simpa only [Structure.Value.prependTokens_eq, List.append_nil] using root.1
    have denotes := (ProfileSemantics.scalar_denotes_iff valid shape).mpr (recovered.trans yield)
    have built := (build_iff tree tokens (ProfileProjection.ofScalar b)).mpr
      ⟨v, structural, denotes⟩
    simp only [buildScalar, built, Option.bind_some, ProfileProjection.scalar_retraction]

theorem buildTensor_tokens_iff (parsed : StructureBridge.parser.run tokens = .ok tree)
    (b : Syntax.TensorBlock) : buildTensor tree tokens = some b ↔ tokens = b.tokens := by
  constructor
  · intro success
    obtain ⟨ast, built, projected⟩ := Option.bind_eq_some_iff.mp success
    have same := ProfileProjection.tensor_projection_exact projected
    subst ast
    obtain ⟨v, _, denotes, yield, valid, shape⟩ := build_sound parsed built
    exact yield.symm.trans ((ProfileSemantics.tensor_denotes_iff valid shape).mp denotes)
  · intro yield
    obtain ⟨v, structural, root⟩ := StructureBridge.build_total parsed
    obtain ⟨valid, shape⟩ := StructureBridge.root_valid parsed root
    have recovered : v.tokens = tokens := by
      simpa only [Structure.Value.prependTokens_eq, List.append_nil] using root.1
    have denotes := (ProfileSemantics.tensor_denotes_iff valid shape).mpr (recovered.trans yield)
    have built := (build_iff tree tokens (ProfileProjection.ofTensor b)).mpr
      ⟨v, structural, denotes⟩
    simp only [buildTensor, built, Option.bind_some, ProfileProjection.tensor_retraction]

theorem buildScalar_eq_decode (parsed : StructureBridge.parser.run tokens = .ok tree) :
    buildScalar tree tokens = Syntax.decode tokens := by
  cases hd : Syntax.decode tokens with
  | none =>
    cases hb : buildScalar tree tokens with
    | none => rfl
    | some b =>
      have yield := (buildScalar_tokens_iff parsed b).mp hb
      have h := Syntax.decode_tokens b
      rw [← yield, hd] at h
      contradiction
  | some b => exact (buildScalar_tokens_iff parsed b).mpr (Syntax.tokens_of_decode hd)

theorem buildTensor_eq_decode (parsed : StructureBridge.parser.run tokens = .ok tree) :
    buildTensor tree tokens = Syntax.decodeTensor tokens := by
  cases hd : Syntax.decodeTensor tokens with
  | none =>
    cases hb : buildTensor tree tokens with
    | none => rfl
    | some b =>
      have yield := (buildTensor_tokens_iff parsed b).mp hb
      have h := Syntax.decodeTensor_tokens b
      rw [← yield, hd] at h
      contradiction
  | some b => exact (buildTensor_tokens_iff parsed b).mpr (Syntax.tokens_of_decodeTensor hd)

end Rumoca.GALEC.Structural
