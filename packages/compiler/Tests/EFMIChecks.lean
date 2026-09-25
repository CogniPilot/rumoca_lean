import ProofAudit.Audit
import Rumoca.EFMIManifestProofs
import Rumoca.EFMIArchiveProofs
import Rumoca.EFMIInitializationProofs
import Rumoca.EFMITensorAlgorithm
import Rumoca.EFMITensorProduction
import GALECParser.Certificate

#audit axioms Rumoca.EFMI.manifests_correct
#audit axioms Rumoca.EFMI.manifests_correct_of_documents
#audit axioms Rumoca.EFMI.ManifestContract.source_name
#audit axioms Rumoca.EFMI.ManifestContract.status_observations
#audit axioms Rumoca.EFMI.archive_correct
#audit axioms Rumoca.EFMI.ArchiveContract.code_members
#audit axioms Rumoca.EFMI.ArchiveContract.schema_members
#audit axioms Rumoca.EFMI.ArchiveContract.roster
#audit axioms Rumoca.EFMI.archive_code_correct
#audit axioms Rumoca.EFMI.efmu_archive_correct
#audit axioms Rumoca.EFMI.compile_archive_verified
#audit axioms Rumoca.EFMI.ProductionContract.startup_source
#audit axioms Rumoca.EFMI.ArchiveContract.startup_source

namespace Rumoca.EFMIChecks
open Rumoca.Tensor

/-! Static-semantics rejection of GALEC texts that the general grammar accepts.
Each text is printed from a changed emitted tree and certified to parse to that
tree; whole-block preparation under the target Integer ceiling then rejects it,
so one-pass source preparation of the actual text fails. -/

section Rejected
open GALEC GALEC.Elaboration GALEC.Elaboration.Surface

private def unitTree : AST.Block := EFMI.scalarBlock

private def real (kind : AST.Kind) (name : String) (extents : List AST.Expr := []) :
    AST.Declaration :=
  ⟨kind, .literal "Real", extents, .ident name⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/- Block end name differs from the block name. -/
certify_source endName (Print.block { unitTree with endName := .ident "Different" })
/- Assignment to an undeclared state entity. -/
certify_source undeclared (Print.block { unitTree with
  methods := [Scalar.startupMethod "missing" "samplePeriod", Scalar.recalibrateMethod,
    Scalar.stepMethod "x"] })
/- Two declarations with the same name. -/
certify_source duplicate (Print.block { unitTree with
  protectedDeclarations := [Scalar.clockDeclaration "samplePeriod", real .constant "x"] })
/- A Real literal outside the admitted values. -/
certify_source literal (Print.block { unitTree with
  methods := [Scalar.startupMethod "x" "samplePeriod", Scalar.recalibrateMethod,
    ⟨.ident "DoStep", [.assign (stateReference "x" []) (.parens (.binary (.literal "+")
      (.reference (stateReference "x" [])) (.literal (.number "2.0"))))], .ident "DoStep"⟩] })
/- A method whose end name differs from its name. -/
certify_source methodEnd (Print.block { unitTree with
  methods := [Scalar.startupMethod "x" "samplePeriod", ⟨.ident "Recalibrate", [], .ident "Startup"⟩,
    Scalar.stepMethod "x"] })
/- A direction in the protected section. -/
certify_source protectedInput (Print.block { unitTree with
  protectedDeclarations := [Scalar.clockDeclaration "samplePeriod", real .input "extra"] })
/- `constant` in the leading section. -/
certify_source publicConstant (Print.block { unitTree with
  publicDeclarations := [Scalar.stateDeclaration "x", real .constant "extra"] })
/- A non-canonical extent numeral. -/
certify_source leadingZero (Print.block { Square.source EFMI.squareExtent with
  publicDeclarations := real .input "u" [.literal (.number "02")] ::
    (Square.squarePublic EFMI.squareExtent).tail })
/- The middle expression of a three-part range is its step: `1:size(self.u, 1):1`
has a non-unit step and is rejected. -/
certify_source swappedRange (Print.block { Square.source EFMI.squareExtent with
  methods := [Square.startupMethod, Scalar.recalibrateMethod,
    ⟨.ident "DoStep", [.forLoop (.ident "k") (natural 1) (some (dimension "u" 1)) (natural 1)
      [.assign (stateReference "x" [iterator "k"]) (.binary (.literal "*")
        (.reference (stateReference "u" [iterator "k"])) (.reference (stateReference "u" [iterator "k"])))],
      Square.clearSource "J", Square.scatterSource "u" "J"], .ident "DoStep"⟩] })

private theorem rejected (witness : Syntax.Witness source block)
    (none : (Block.fromBlock Static.Bounded.integerCeiling block).isNone = true) :
    ∀ product, Block.fromSource source ≠ .ok product :=
  Block.fromSource_rejected witness (Option.isNone_iff_eq_none.mp none)

theorem end_name_rejected : ∀ product, Block.fromSource endName.source ≠ .ok product :=
  rejected endName.witness (by decide +kernel)
theorem undeclared_rejected : ∀ product, Block.fromSource undeclared.source ≠ .ok product :=
  rejected undeclared.witness (by decide +kernel)
theorem duplicate_rejected : ∀ product, Block.fromSource duplicate.source ≠ .ok product :=
  rejected duplicate.witness (by decide +kernel)
theorem literal_rejected : ∀ product, Block.fromSource literal.source ≠ .ok product :=
  rejected literal.witness (by decide +kernel)
theorem method_end_rejected : ∀ product, Block.fromSource methodEnd.source ≠ .ok product :=
  rejected methodEnd.witness (by decide +kernel)
theorem protected_input_rejected : ∀ product, Block.fromSource protectedInput.source ≠ .ok product :=
  rejected protectedInput.witness (by decide +kernel)
theorem public_constant_rejected : ∀ product, Block.fromSource publicConstant.source ≠ .ok product :=
  rejected publicConstant.witness (by decide +kernel)
theorem leading_zero_rejected : ∀ product, Block.fromSource leadingZero.source ≠ .ok product :=
  rejected leadingZero.witness (by decide +kernel)
theorem swapped_range_rejected : ∀ product, Block.fromSource swappedRange.source ≠ .ok product :=
  rejected swappedRange.witness (by decide +kernel)

/-- The same edits without their faults prepare: an unused protected constant,
an unused leading variable and a second distinct protected constant. Each
rejection above is therefore caused by its one fault. -/
theorem single_faults :
    (Block.fromBlock Static.Bounded.integerCeiling { unitTree with
      protectedDeclarations := [Scalar.clockDeclaration "samplePeriod", real .constant "extra"] }).isSome ∧
    (Block.fromBlock Static.Bounded.integerCeiling { unitTree with
      publicDeclarations := [Scalar.stateDeclaration "x", real .variable "extra"] }).isSome ∧
    (Block.fromBlock Static.Bounded.integerCeiling { unitTree with
      protectedDeclarations := [Scalar.clockDeclaration "samplePeriod", real .constant "y"] }).isSome := by
  decide +kernel

/- A different well-formed program: DoStep reads the period instead of `x`. -/
certify_source readsPeriod (Print.block { unitTree with
  methods := [Scalar.startupMethod "x" "samplePeriod", Scalar.recalibrateMethod,
    ⟨.ident "DoStep", [.assign (stateReference "x" []) (.parens (.binary (.literal "+")
      (.reference (stateReference "samplePeriod" [])) (.literal (.number "1.0"))))],
      .ident "DoStep"⟩] })

/-- A different well-formed program is not the scalar builder's tree, so the
scalar source semantics rejects it for every prepared block. This is a
syntactic rejection: the parsed tree differs from the builder's tree. -/
theorem reads_period_rejected (block : Solve.Algorithm.Block scalar) :
    ¬ EFMI.ScalarSourceSemantics readsPeriod.ast block := by
  intro semantics
  have printed := congrArg Print.block semantics.source
  exact absurd printed (by decide +kernel)

end Rejected

/-- A prepared block with a zero period program is not the meaning of the
emitted source: its Startup leaves a different sample period. -/
theorem changed_period :
    ¬ EFMI.ScalarSourceSemantics EFMI.scalarBlock
      { Solve.Algorithm.unitBlock with startupPeriod := .fill .zero (.ret .here) } := by
  intro semantics
  let state : GALEC.UnitProfile.State Binary64.Value :=
    ⟨Value.fill scalar Binary64.one, Value.fill scalar Binary64.one⟩
  have same := (semantics.execution 0 .startup state _).mp
    ((EFMI.scalar_source_semantics rfl rfl).refines 0 .startup state)
  have period := congrArg (fun after : GALEC.UnitProfile.State Binary64.Value =>
    after.samplePeriod[0]'(by decide)) same
  exact absurd period (by decide +kernel)

#audit axioms Solve.Algorithm.lower_equation_correct
#audit axioms Solve.Algorithm.prepare_step_correct
#audit axioms Solve.Algorithm.unit_no_overflow
#audit axioms Solve.Algorithm.Model.startup_correct
#audit axioms Solve.Algorithm.Model.recalibrate_correct
#audit axioms Solve.Algorithm.Model.doStep_correct
#audit axioms Solve.Algorithm.Model.run_correct
#audit axioms EFMI.AlgorithmContract.solve_refinement
#audit axioms EFMI.AlgorithmContract.lifecycle_refinement
#audit axioms EFMI.algorithm_correct
#audit axioms EFMI.compile_algorithm_verified
#audit axioms EFMI.production_correct
#audit axioms EFMI.ProductionContract.original_methods
#audit axioms EFMI.compile_production_verified
#audit axioms Rumoca.square_prepared_kernel
#audit axioms Rumoca.TensorAlgorithmArtifact.algorithm_correct
#audit axioms Rumoca.squareAlgorithmArtifact
#audit axioms Rumoca.TensorProductionArtifact.production_correct
#audit axioms Rumoca.TensorProductionArtifact.manifests_correct
#audit axioms Rumoca.squareProductionArtifact
#audit axioms end_name_rejected
#audit axioms undeclared_rejected
#audit axioms duplicate_rejected
#audit axioms literal_rejected
#audit axioms method_end_rejected
#audit axioms protected_input_rejected
#audit axioms public_constant_rejected
#audit axioms leading_zero_rejected
#audit axioms swapped_range_rejected
#audit axioms single_faults
#audit axioms reads_period_rejected
#audit axioms changed_period

end Rumoca.EFMIChecks
