import RumocaCore.Initialization.Diagnostics
import ModelicaParser.LocatedProofs

namespace Rumoca.Initialization

theorem diagnostics_notice (plan : Plan Nat) (state : String) (span : Parser.Source.Span source)
    (notice : Notice) (member : notice ∈ plan.notices) :
    (⟨"initialization", span, notice.message state plan.initial, []⟩ : Parser.Source.Diagnostic source)
      ∈ diagnostics plan state span := List.mem_map.mpr ⟨notice, member, rfl⟩

theorem diagnostics_span (plan : Plan Nat) (state : String) (span : Parser.Source.Span source)
    (diagnostic : Parser.Source.Diagnostic source) (member : diagnostic ∈ diagnostics plan state span) :
    diagnostic.span = span := by
  obtain ⟨notice, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem forModel_state (input : Parser.Source.InputRef) (parsed : LocatedParsed input.source)
    (resolved : AST.Resolved parsed.parsed.ast) (diagnostic : Parser.Source.Diagnostic input.source)
    (member : diagnostic ∈ forModel input parsed resolved) :
    diagnostic.span.text = parsed.parsed.ast.state := by
  have span := diagnostics_span _ _ _ diagnostic member
  rw [span]
  exact parsed.state_field_text

theorem forModel_notices (input : Parser.Source.InputRef) (parsed : LocatedParsed input.source)
    (resolved : AST.Resolved parsed.parsed.ast) :
    forModel input parsed resolved =
      diagnostics ⟨0, [.fallbackUsed, .unfixedStartSelected]⟩ parsed.parsed.ast.state (parsed.fieldSpan 3) := by
  dsimp only [forModel]
  rw [Solve.Model.initial_default]

end Rumoca.Initialization
