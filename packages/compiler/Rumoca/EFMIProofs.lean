import Rumoca.EFMI
import Rumoca.GALEC
import RumocaEFMI.AlgorithmProofs
import RumocaCore.GALEC.Protocol

open _root_.Parser

noncomputable section
namespace Rumoca.EFMI

/-- Contract for the actual Algorithm Code member. This does not certify a
Production Code member, XML, checksums, ZIP, or the host lifecycle scheduler. -/
structure AlgorithmContract (a : Artifact source) (emitted : String) : Prop where
  bytes : a.algorithmSource = emitted
  source_lexes : Lexes source.source.toList a.parsed.ast.tokens
  source_ebnf : EBNF.Accepts Generated.sourceGrammar (a.parsed.tokens.map Token.symbol)
  grammar_processed :
    (LALR.Frontend.compile GALEC.Generated.source).map (·.grammar) = .ok GALEC.Generated.grammar
  parsed : ∃ p, GALEC.Syntax.parse emitted = .ok p ∧ Denotes p.ast a.algorithmCode.block
  dae_admission : ∀ dx : ℝ, a.solve.dae.Holds dx ↔ dx = 1
  startup : ∀ x, a.algorithmCode.execute .startup x = Binary64.positiveZero
  recalibrate : ∀ x, a.algorithmCode.execute .recalibrate x = x
  step : ∀ x, a.algorithmCode.execute .doStep x = a.solve.advance x
  samples : ∀ x n, a.algorithmCode.run x n = a.solve.run x n
  solve_refinement : ∀ method (state : GALEC.UnitProfile.State Binary64.Value),
    GALEC.UnitProfile.solveExecute (Solve.Algorithm.lower a.algorithmCode.block)
      Binary64.positiveZero Binary64.one GALEC.roundedAdd method state =
    GALEC.UnitProfile.execute a.algorithmCode.block
      Binary64.positiveZero Binary64.one GALEC.roundedAdd method state
  lifecycle_refinement : ∀ (before after : GALEC.Protocol.Configuration Binary64.Value) events,
    GALEC.Protocol.Trace
      (GALEC.UnitProfile.solveExecute (Solve.Algorithm.lower a.algorithmCode.block)
        Binary64.positiveZero Binary64.one GALEC.roundedAdd) before events after ↔
    GALEC.Protocol.Trace
      (GALEC.UnitProfile.execute a.algorithmCode.block
        Binary64.positiveZero Binary64.one GALEC.roundedAdd) before events after

theorem algorithm_correct (a : Artifact source) (he : a.algorithmSource = emitted) :
    AlgorithmContract a emitted := by
  refine ⟨he, parsed_lexes a.parsed, parsed_in_ebnf a.parsed, EFMI.grammar_processed,
    he ▸ render_denotes a.algorithmCode, GALEC.lower_equation_correct a.solve.dae,
    GALEC.startup_correct _, GALEC.recalibrate_correct _, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [GALEC.doStep_correct, Solve.Model.advance_correct]
  · intro x n
    rw [GALEC.run_correct, Solve.Model.run_correct]
  · exact fun method state => GALEC.UnitProfile.lower_correct _ _ _ _ method state
  · exact GALEC.Protocol.lower_trace_correct _ _ _ _

theorem compile_algorithm_verified (h : compile source = .ok a)
    (he : a.algorithmSource = emitted) :
    compile source = .ok a ∧ AlgorithmContract a emitted := ⟨h, algorithm_correct a he⟩

end Rumoca.EFMI
