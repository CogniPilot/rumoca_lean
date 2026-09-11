import Rumoca.InitializationDiagnostics
import RumocaCore.Initialization.DiagnosticProofs

namespace Rumoca

/-- Compiler notices agree with the shared editor analysis for the same
immutable input and parse, without a second parse or a location fallback. -/
theorem Artifact.initializationDiagnostics_eq_forModel (artifact : Artifact input) :
    artifact.initializationDiagnostics =
      Initialization.forModel input artifact.located artifact.solve.dae.flat.resolved := by
  dsimp only [initializationDiagnostics, Initialization.forModel]
  rw [artifact.solve.initial_default, Solve.Model.initial_default]
  rfl

/-- Every notice is retained using the artifact's required source provenance. -/
theorem Artifact.initializationDiagnostic_count (artifact : Artifact source) :
    artifact.initializationDiagnostics.length = artifact.solve.initial.notices.length := by
  simp [initializationDiagnostics, Initialization.diagnostics]

theorem Artifact.initializationDiagnostic_state (artifact : Artifact source)
    (diagnostic : Parser.Source.Diagnostic source.source)
    (member : diagnostic ∈ artifact.initializationDiagnostics) :
    diagnostic.span.text = artifact.parsed.ast.state := by
  have span := Initialization.diagnostics_span _ _ _ diagnostic member
  rw [span]
  exact artifact.located.state_field_text

end Rumoca
