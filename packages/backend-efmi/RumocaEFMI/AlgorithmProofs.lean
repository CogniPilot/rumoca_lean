import RumocaEFMI.AlgorithmCode
import RumocaCore.GALEC.UnitProfile
import RumocaCore.GALEC.Elaboration.Scalar.Preparation
import GALECParser.GrammarProofs
import GALECParser.Certificate

open _root_.Parser

namespace Rumoca.EFMI

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/- Kernel-checked parse of the emitted scalar Algorithm Code text. -/
certify_source unitAlgorithm unitSource

/-- The parsed tree of the emitted scalar text is the scalar specification tree
of the core preparation and state proofs, with the emitted names. -/
theorem unit_ast :
    unitAlgorithm.ast = GALEC.Elaboration.Scalar.source "UnitIntegrator" "x" "samplePeriod" := rfl

/-- Actual source grammar processing is checked in Lean, independently of the
native table producer. The general metalanguage/desugaring theorem is still
open; this equality binds this concrete generated CFG to its EBNF bytes. -/
theorem grammar_processed :
    (LALR.Frontend.compile GALEC.Generated.source).map (·.grammar) =
      .ok GALEC.Generated.grammar := GALEC.Generated.grammar_processed

theorem render_parses (m : GALEC.Model source) :
    ∃ parsed, GALEC.Syntax.parse (renderAlgorithm m) = .ok parsed ∧
      parsed.ast = GALEC.Elaboration.Scalar.source "UnitIntegrator" "x" "samplePeriod" := by
  rw [emission_is_unit]
  obtain ⟨parsed, accepted, same⟩ := unitAlgorithm.parsed
  exact ⟨parsed, accepted, same.trans unit_ast⟩

/-- The parsed source is the scalar specification tree and the checked block is
the admitted lifecycle block, including the sampling-period initialization. -/
def Denotes (parsed : GALEC.AST.Block) (block : GALEC.Block Rumoca.Tensor.scalar) : Prop :=
  parsed = GALEC.Elaboration.Scalar.source "UnitIntegrator" "x" "samplePeriod" ∧
    block = GALEC.unitBlock

theorem render_denotes (m : GALEC.Model source) :
    ∃ parsed, GALEC.Syntax.parse (renderAlgorithm m) = .ok parsed ∧ Denotes parsed.ast m.block := by
  obtain ⟨p, hp, hast⟩ := render_parses m
  exact ⟨p, hp, hast, m.profile⟩

end Rumoca.EFMI
