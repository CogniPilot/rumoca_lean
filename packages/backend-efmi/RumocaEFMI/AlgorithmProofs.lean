import RumocaEFMI.AlgorithmCode
import RumocaCore.GALEC.Elaboration.Scalar.State
import RumocaCore.GALEC.Elaboration.Scalar.FiniteArithmetic
import RumocaCore.GALEC.Elaboration.Block.Source
import RumocaCore.GALEC.Protocol
import GALECParser.GrammarProofs
import GALECParser.Certificate

/-! Original-body semantics of the emitted scalar Algorithm Code. The emitted
text is certified to parse to the builder's tree; one-pass source preparation
returns that tree, and its selected method bodies execute exactly as the
prepared Solve block, on the logical state used by the Production Code
contract. -/
open _root_.Parser

noncomputable section
namespace Rumoca.EFMI
open GALEC.Elaboration

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/- Kernel-checked parse of the emitted scalar Algorithm Code text. -/
certify_source unitAlgorithm (GALEC.Print.block scalarBlock)

/-- The parsed tree of the emitted scalar text is the builder's tree. -/
theorem unit_ast : unitAlgorithm.ast = scalarBlock := rfl

/-- Actual source grammar processing is checked in Lean, independently of the
native table producer. The general metalanguage/desugaring theorem is still
open; this equality binds this concrete generated CFG to its EBNF bytes. -/
theorem grammar_processed :
    (LALR.Frontend.compile GALEC.Generated.source).map (·.grammar) =
      .ok GALEC.Generated.grammar := GALEC.Generated.grammar_processed

theorem render_parses (model : Solve.Algorithm.Model source) :
    ∃ parsed, GALEC.Syntax.parse (renderAlgorithm model) = .ok parsed ∧
      parsed.ast = scalarBlock := by
  obtain ⟨parsed, accepted, same⟩ := unitAlgorithm.parsed
  exact ⟨parsed, accepted, same.trans unit_ast⟩

theorem emitted_prepared (model : Solve.Algorithm.Model source) :
    ∃ product, Block.fromSource (renderAlgorithm model) = .ok product ∧
      product.result = Scalar.result "UnitIntegrator" "x" "samplePeriod" :=
  (Block.fromSource_iff _ _).mpr ⟨scalarBlock, unit_ast ▸ unitAlgorithm.witness,
    Scalar.prepared _ (by decide) _⟩

/-- The source tree prepares to the scalar results at every ceiling, and each
selected source method executes, on the shared logical state, exactly as the
prepared Solve block `block`. -/
structure ScalarSourceSemantics (parsed : GALEC.AST.Block)
    (block : Solve.Algorithm.Block Tensor.scalar) : Prop where
  source : parsed = scalarBlock
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
    Scalar.StateBridge.SourceExec parsed "x" "samplePeriod" ceiling Solve.Tensor.Finite.Result
      Binary64.positiveZero Binary64.one method before after ↔
      after = GALEC.UnitProfile.solveExecute block Binary64.positiveZero Binary64.one
        GALEC.roundedAdd method before

theorem scalar_source_semantics (source : parsed = scalarBlock)
    (profile : block = Solve.Algorithm.unitBlock) : ScalarSourceSemantics parsed block := by
  subst source
  subst profile
  have different : "x" ≠ "samplePeriod" := by decide
  refine ⟨rfl, Scalar.prepared "UnitIntegrator" different, Scalar.startup_lowered _ different,
    Scalar.recalibrate_lowered _ different, Scalar.step_lowered _ different, ?_⟩
  intro ceiling method before after
  exact Scalar.StateBridge.sourceExec_iff_solve (Scalar.prepared "UnitIntegrator" different ceiling)
    Solve.Tensor.Finite.Result Binary64.positiveZero Binary64.one GALEC.roundedAdd
    Scalar.finite_add_one method before after

/-- The Solve result of every method is a source execution of that method. -/
theorem ScalarSourceSemantics.refines (semantics : ScalarSourceSemantics parsed block)
    (ceiling : Nat) (method : GALEC.Method) (before : GALEC.UnitProfile.State Binary64.Value) :
    Scalar.StateBridge.SourceExec parsed "x" "samplePeriod" ceiling Solve.Tensor.Finite.Result
      Binary64.positiveZero Binary64.one method before
      (GALEC.UnitProfile.solveExecute block Binary64.positiveZero Binary64.one
        GALEC.roundedAdd method before) :=
  (semantics.execution ceiling method before _).mpr rfl

/-- Every method executor that realizes the source methods has exactly the
lifecycle traces of the Solve block, including visible state and the count of
completed sampling calls. -/
theorem ScalarSourceSemantics.lifecycle (semantics : ScalarSourceSemantics parsed block)
    (ceiling : Nat)
    (execute : GALEC.Method → GALEC.UnitProfile.State Binary64.Value →
      GALEC.UnitProfile.State Binary64.Value)
    (realizes : ∀ method before, Scalar.StateBridge.SourceExec parsed "x" "samplePeriod" ceiling
      Solve.Tensor.Finite.Result Binary64.positiveZero Binary64.one method before
      (execute method before))
    (before after : GALEC.Protocol.Configuration Binary64.Value) (events : List GALEC.Protocol.Event) :
    GALEC.Protocol.Trace execute before events after ↔
      GALEC.Protocol.Trace (GALEC.UnitProfile.solveExecute block Binary64.positiveZero
        Binary64.one GALEC.roundedAdd) before events after :=
  GALEC.Protocol.trace_congr fun method state =>
    (semantics.execution ceiling method state _).mp (realizes method state)

theorem render_source_semantics (model : Solve.Algorithm.Model source) :
    ∃ product, Block.fromSource (renderAlgorithm model) = .ok product ∧
      ScalarSourceSemantics product.parsed.ast model.block := by
  obtain ⟨product, compiled, _⟩ := emitted_prepared model
  exact ⟨product, compiled, scalar_source_semantics
    ((GALEC.Syntax.witness_unique product.parsed.witnessed unitAlgorithm.witness).trans unit_ast)
    model.profile⟩

end Rumoca.EFMI
