import RumocaEFMI.AlgorithmProofs
import RumocaCore.GALEC.Elaboration.Scalar.State
import RumocaCore.GALEC.Elaboration.Scalar.FiniteArithmetic

/-! Original scalar Algorithm Code bodies through generic preparation to the
same logical state used by the existing Solve/C contract. This is proof-side
composition, not backend name resolution or a new source admission. -/
noncomputable section
namespace Rumoca.EFMI
open GALEC.Elaboration

structure ScalarSourceSemantics (parsed : GALEC.Syntax.Block)
    (block : GALEC.Block Tensor.scalar) : Prop where
  resolved : GALEC.Syntax.Resolved parsed
  startup_prepared : ∀ ceiling,
    Methods.Preparation.fromBlock (.literal "Startup") Capabilities.Initialization.role ceiling
      (GALEC.ProfileProjection.ofScalar parsed) = some (Scalar.startupResult parsed)
  recalibrate_prepared : ∀ ceiling,
    Methods.Preparation.fromBlock (.literal "Recalibrate") Capabilities.DoStep.role ceiling
      (GALEC.ProfileProjection.ofScalar parsed) = some (Scalar.recalibrateResult parsed)
  step_prepared : ∀ ceiling,
    Methods.Preparation.fromBlock (.literal "DoStep") Capabilities.DoStep.role ceiling
      (GALEC.ProfileProjection.ofScalar parsed) = some (Scalar.stepResult parsed)
  execution : ∀ ceiling method (before after : GALEC.UnitProfile.State Binary64.Value),
    Scalar.StateBridge.SourceExec parsed ceiling Solve.Tensor.Finite.Result
      Binary64.positiveZero Binary64.one method before after ↔
      after = GALEC.UnitProfile.execute block Binary64.positiveZero Binary64.one
        GALEC.roundedAdd method before

theorem scalar_source_semantics (denotes : Denotes parsed block) :
    ScalarSourceSemantics parsed block := by
  refine ⟨denotes.1, Scalar.startup_lowered parsed denotes.1,
    Scalar.recalibrate_lowered parsed denotes.1, Scalar.step_lowered parsed denotes.1, ?_⟩
  intro ceiling method before after
  rw [denotes.2]
  exact Scalar.StateBridge.sourceExec_iff_unitBlock parsed denotes.1 ceiling Solve.Tensor.Finite.Result
    Binary64.positiveZero Binary64.one GALEC.roundedAdd Scalar.finite_add_one method before after

theorem render_source_semantics (model : GALEC.Model source) :
    ∃ parsed, GALEC.Syntax.parse (renderAlgorithm model) = .ok parsed ∧
      ScalarSourceSemantics parsed.ast model.block := by
  obtain ⟨parsed, accepted, denotes⟩ := render_denotes model
  exact ⟨parsed, accepted, scalar_source_semantics denotes⟩

end Rumoca.EFMI
