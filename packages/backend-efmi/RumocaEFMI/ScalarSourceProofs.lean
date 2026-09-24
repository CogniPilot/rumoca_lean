import RumocaEFMI.AlgorithmProofs
import RumocaCore.GALEC.Elaboration.Scalar.State
import RumocaCore.GALEC.Elaboration.Scalar.FiniteArithmetic

/-! Original scalar Algorithm Code bodies through generic preparation to the
same logical state used by the existing Solve/C contract. This is proof-side
composition, not backend name resolution or a new source admission. -/
noncomputable section
namespace Rumoca.EFMI
open GALEC.Elaboration

structure ScalarSourceSemantics (parsed : GALEC.AST.Block)
    (block : GALEC.Block Tensor.scalar) : Prop where
  source : parsed = Scalar.source "UnitIntegrator" "x" "samplePeriod"
  prepared : ∀ ceiling, Block.Prepares ceiling parsed
    (Scalar.result "UnitIntegrator" "x" "samplePeriod")
  startup_prepared : ∀ ceiling,
    Methods.Preparation.fromBlock (.ident "Startup") Capabilities.Initialization.role ceiling
      parsed = some (Scalar.startupResult "x" "samplePeriod")
  recalibrate_prepared : ∀ ceiling,
    Methods.Preparation.fromBlock (.ident "Recalibrate") Capabilities.DoStep.role ceiling
      parsed = some (Scalar.recalibrateResult "x" "samplePeriod")
  step_prepared : ∀ ceiling,
    Methods.Preparation.fromBlock (.ident "DoStep") Capabilities.DoStep.role ceiling
      parsed = some (Scalar.stepResult "x" "samplePeriod")
  execution : ∀ ceiling method (before after : GALEC.UnitProfile.State Binary64.Value),
    Scalar.StateBridge.SourceExec "x" "samplePeriod" ceiling Solve.Tensor.Finite.Result
      Binary64.positiveZero Binary64.one method before after ↔
      after = GALEC.UnitProfile.execute block Binary64.positiveZero Binary64.one
        GALEC.roundedAdd method before

theorem scalar_source_semantics (denotes : Denotes parsed block) :
    ScalarSourceSemantics parsed block := by
  obtain ⟨rfl, rfl⟩ := denotes
  have different : "x" ≠ "samplePeriod" := by decide
  refine ⟨rfl, Scalar.prepared "UnitIntegrator" different, Scalar.startup_lowered _ different,
    Scalar.recalibrate_lowered _ different, Scalar.step_lowered _ different, ?_⟩
  intro ceiling method before after
  exact Scalar.StateBridge.sourceExec_iff_unitBlock different ceiling Solve.Tensor.Finite.Result
    Binary64.positiveZero Binary64.one GALEC.roundedAdd Scalar.finite_add_one method before after

theorem render_source_semantics (model : GALEC.Model source) :
    ∃ parsed, GALEC.Syntax.parse (renderAlgorithm model) = .ok parsed ∧
      ScalarSourceSemantics parsed.ast model.block := by
  obtain ⟨parsed, accepted, denotes⟩ := render_denotes model
  exact ⟨parsed, accepted, scalar_source_semantics denotes⟩

end Rumoca.EFMI
