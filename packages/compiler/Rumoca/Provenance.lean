import Rumoca.Compiler

/-! Source provenance at the actual compiler boundary. Later IR-origin and
emitted-byte mapping obligations are separate from these frontend facts. -/
namespace Rumoca
open _root_.Parser

/-- Every artifact's required locations identify its actual semantic AST fields,
including both resolved references. No attachment-success premise is supplied. -/
theorem Artifact.source_locations (artifact : Artifact source) :
    parse source = .ok artifact.parsed ∧
    (artifact.located.fieldSpan 1).text = artifact.parsed.ast.name ∧
    (artifact.located.fieldSpan 3).text = artifact.parsed.ast.state ∧
    (artifact.located.fieldSpan 8).text = artifact.parsed.ast.state ∧
    (artifact.located.fieldSpan 14).text = artifact.parsed.ast.name := by
  have resolved := artifact.solve.dae.flat.resolved
  refine ⟨artifact.located.erases, ?_, artifact.located.state_field_text, ?_, ?_⟩
  · rw [artifact.located.fieldSpan_eq_tokenSpan]
    simpa using artifact.located.modelName_text
  · rw [artifact.located.fieldSpan_eq_tokenSpan]
    simpa using artifact.located.derivativeName_text.trans resolved.derivative_resolves
  · rw [artifact.located.fieldSpan_eq_tokenSpan]
    simpa using artifact.located.endName_text.trans resolved.end_matches

/-- The production driver retains the resolver's structured diagnostic exactly. -/
theorem compile_resolve_error (parsed : LocatedParsed source)
    (accepted : parseLocated source = .ok parsed) (error : Source.Diagnostic source)
    (rejected : parsed.resolve = .error error) : compile source = .error error := by
  simp [compile, accepted, rejected, bind, Except.bind]

/-- A failure after successful parsing is exactly a located resolution failure;
compiler adaptation cannot replace its primary or related source locations. -/
theorem compile_error_after_parse (parsed : LocatedParsed source)
    (accepted : parseLocated source = .ok parsed) (error : Source.Diagnostic source)
    (rejected : compile source = .error error) : parsed.resolve = .error error := by
  simp only [compile, accepted, bind, Except.bind] at rejected
  cases resolution : parsed.resolve with
  | error diagnostic =>
      rw [resolution] at rejected
      have same : diagnostic = error := Except.error.inj rejected
      subst diagnostic
      rfl
  | ok resolved =>
      rw [resolution] at rejected
      contradiction

end Rumoca
