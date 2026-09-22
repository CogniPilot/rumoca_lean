import GALECParser.Parser

/-! Proof-only profile-decoder specification of the current source entrypoints.
The reference control flow came from the pre-structural cutover (a11e030), but
its grammar/token dependencies follow the current profile. After GJ02 this is
not historical language equality: old dimension placement is intentionally
rejected. Noncomputable definitions prevent a runtime fallback. Exact Except
equality covers current diagnostic precedence and successful ASTs; production
source parsing does not import these definitions. -/
namespace Rumoca.GALEC.Syntax.Compatibility
open _root_.Parser

private theorem tree_language (parsed : parseTree tokens = .ok tree) :
    Generated.grammar.Accepts (tokens.map encode) := by
  have accepted := (Generated.parse_correct
    ((tokens.map Token.symbol).map Generated.encode)).1.mpr ⟨tree, parsed⟩
  simpa only [List.map_map, Function.comp_def, encode] using accepted


noncomputable def scalarReference (source : String) : Except Diagnostic (Parsed source) :=
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


noncomputable def tensorReference (source : String) : Except Diagnostic (TensorParsed source) :=
  match hl : Scanner.lex tensorScanner source with
  | .error e => .error e
  | .ok tokens => match ht : parseTree tokens with
    | .error _ => .error ⟨"GALEC syntax", 0, "outside the certified tensor grammar profile"⟩
    | .ok _tree => match ha : decodeTensor tokens with
      | none => .error ⟨"GALEC action", 0, "outside the tensor square action profile"⟩
      | some ast =>
        if hr : ResolvedTensor ast then
          .ok ⟨ast, tokens_of_decodeTensor ha ▸ (Scanner.lex_correct tensorScanner source tokens).mp hl,
            tokens_of_decodeTensor ha ▸ tree_language ht, hr⟩
        else .error ⟨"GALEC resolve", 0, "mismatched tensor block/state/input name"⟩


/-- Exact structural-parser/specification result, including diagnostics. -/
theorem scalar_reference_exact (source : String) : parse source = scalarReference source := by
  have action : ∀ tokens tree, parseTree tokens = .ok tree →
      Structural.buildScalar tree tokens = decode tokens :=
    fun _ _ parsed => Structural.buildScalar_eq_decode parsed
  unfold parse scalarReference
  repeat' first | (simp_all; done) | split
  all_goals simp_all
  all_goals (subst_vars; simp_all)

theorem tensor_reference_exact (source : String) : parseTensor source = tensorReference source := by
  have action : ∀ tokens tree, parseTree tokens = .ok tree →
      Structural.buildTensor tree tokens = decodeTensor tokens :=
    fun _ _ parsed => Structural.buildTensor_eq_decode parsed
  unfold parseTensor tensorReference
  repeat' first | (simp_all; done) | split
  all_goals simp_all
  all_goals (subst_vars; simp_all)

end Rumoca.GALEC.Syntax.Compatibility
