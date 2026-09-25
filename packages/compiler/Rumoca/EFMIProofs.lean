import Rumoca.EFMI
import Rumoca.AlgorithmSemantics
import RumocaEFMI.AlgorithmProofs

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
  parsed : ∃ p, GALEC.Syntax.parse emitted = .ok p ∧ p.ast = scalarBlock ∧
    a.algorithmSolve.block = Solve.Algorithm.unitBlock
  original_source : ∃ product, GALEC.Elaboration.Block.fromSource emitted = .ok product ∧
    ScalarSourceSemantics product.parsed.ast a.algorithmSolve.block
  dae_admission : ∀ dx : ℝ, a.solve.dae.Holds dx ↔ dx = 1
  startup : ∀ x, a.algorithmSolve.execute .startup x = Binary64.positiveZero
  recalibrate : ∀ x, a.algorithmSolve.execute .recalibrate x = x
  step : ∀ x, a.algorithmSolve.execute .doStep x = a.solve.advance x
  samples : ∀ x n, a.algorithmSolve.run x n = a.solve.run x n

theorem algorithm_correct (a : Artifact source) (he : a.algorithmSource = emitted) :
    AlgorithmContract a emitted := by
  subst emitted
  obtain ⟨parsed, accepted, same⟩ := render_parses a.algorithmSolve
  refine ⟨rfl, parsed_lexes a.parsed, parsed_in_ebnf a.parsed, EFMI.grammar_processed,
    ⟨parsed, accepted, same, a.algorithmSolve.profile⟩, render_source_semantics a.algorithmSolve,
    Solve.Algorithm.lower_equation_correct a.solve.dae,
    Solve.Algorithm.Model.startup_correct _, Solve.Algorithm.Model.recalibrate_correct _, ?_, ?_⟩
  · intro x
    rw [Solve.Algorithm.Model.doStep_correct, Solve.Model.advance_correct]
  · intro x n
    rw [Solve.Algorithm.Model.run_correct, Solve.Model.run_correct]

/-- Every prepared Solve method result is an original source execution of the
emitted text's selected method, at every ceiling and for every state. -/
theorem AlgorithmContract.solve_refinement (contract : AlgorithmContract a emitted) :
    ∃ product, GALEC.Elaboration.Block.fromSource emitted = .ok product ∧
      ∀ ceiling method (state : GALEC.UnitProfile.State Binary64.Value),
        GALEC.Elaboration.Scalar.StateBridge.SourceExec product.parsed.ast GALEC.Names.state GALEC.Names.clock
          ceiling Solve.Tensor.Finite.Result Binary64.positiveZero Binary64.one method state
          (GALEC.UnitProfile.solveExecute a.algorithmSolve.block Binary64.positiveZero
            Binary64.one GALEC.roundedAdd method state) := by
  obtain ⟨product, compiled, semantics⟩ := contract.original_source
  exact ⟨product, compiled, semantics.refines⟩

/-- Every executor realizing the emitted text's original source methods has
exactly the lifecycle traces of the prepared Solve block. -/
theorem AlgorithmContract.lifecycle_refinement (contract : AlgorithmContract a emitted) :
    ∃ product, GALEC.Elaboration.Block.fromSource emitted = .ok product ∧
      ∀ ceiling (execute : GALEC.Method → GALEC.UnitProfile.State Binary64.Value →
          GALEC.UnitProfile.State Binary64.Value),
        (∀ method before, GALEC.Elaboration.Scalar.StateBridge.SourceExec product.parsed.ast
          GALEC.Names.state GALEC.Names.clock ceiling Solve.Tensor.Finite.Result Binary64.positiveZero
          Binary64.one method before (execute method before)) →
        ∀ (before after : GALEC.Protocol.Configuration Binary64.Value) events,
          GALEC.Protocol.Trace execute before events after ↔
            GALEC.Protocol.Trace (GALEC.UnitProfile.solveExecute a.algorithmSolve.block
              Binary64.positiveZero Binary64.one GALEC.roundedAdd) before events after := by
  obtain ⟨product, compiled, semantics⟩ := contract.original_source
  exact ⟨product, compiled, semantics.lifecycle⟩

theorem compile_algorithm_verified (h : compile source = .ok a)
    (he : a.algorithmSource = emitted) :
    compile source = .ok a ∧ AlgorithmContract a emitted := ⟨h, algorithm_correct a he⟩

end Rumoca.EFMI
