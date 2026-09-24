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

private def unitTree : AST.Block := Scalar.source "UnitIntegrator" "x" "samplePeriod"

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
certify_source duplicate (Print.block { unitTree with protectedDeclarations := [real .constant "x"] })
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
  protectedDeclarations := [real .input "samplePeriod"] })
/- `constant` in the leading section. -/
certify_source publicConstant (Print.block { unitTree with
  publicDeclarations := [real .constant "x"] })
/- A non-canonical extent numeral. -/
certify_source leadingZero (Print.block { EFMI.squareBlock EFMI.squareExtent with
  publicDeclarations := real .input "u" [.literal (.number "02")] ::
    (Square.squarePublic EFMI.squareExtent).tail })
/- The middle expression of a three-part range is its step: `1:size(self.u, 1):1`
has a non-unit step and is rejected. -/
certify_source swappedRange (Print.block { EFMI.squareBlock EFMI.squareExtent with
  methods := [EFMI.squareStartup, Scalar.recalibrateMethod,
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

/- A different well-formed program: DoStep reads the period instead of `x`. -/
certify_source readsPeriod (Print.block { unitTree with
  methods := [Scalar.startupMethod "x" "samplePeriod", Scalar.recalibrateMethod,
    ⟨.ident "DoStep", [.assign (stateReference "x" []) (.parens (.binary (.literal "+")
      (.reference (stateReference "samplePeriod" [])) (.literal (.number "1.0"))))],
      .ident "DoStep"⟩] })

/-- The compiler's scalar Algorithm Code denotation rejects a different
well-formed program, not only malformed or unprepared text. -/
theorem reads_period_rejected : ¬ EFMI.Denotes readsPeriod.ast GALEC.unitBlock := by
  intro denotes
  have printed := congrArg Print.block denotes.1
  exact absurd printed (by decide +kernel)

end Rejected

theorem changed_period :
    ¬ EFMI.Denotes (GALEC.Elaboration.Scalar.source "UnitIntegrator" "x" "samplePeriod")
      { GALEC.unitBlock with startupPeriod := .zero } := by
  intro h
  have hc : (GALEC.Expr.zero : GALEC.Expr scalar) = .one :=
    congrArg (·.startupPeriod) h.2
  cases hc

/-- The arithmetic interpretation is deliberately order-sensitive. All six
coordinates survive without changing the tensor shape during compilation. -/
theorem tensor_operation_order :
    ((Solve.Algorithm.compileExpr (.add .state (.add .one .one))).eval
      0 1 (fun a b : Nat => 10 * a + b)
      (Solve.Tensor.Env.push (Value.fill ⟨[2, 3]⟩ 2) Solve.Tensor.Env.empty)).data.toArray =
        #[31, 31, 31, 31, 31, 31] := by decide +kernel

theorem initial_state_and_period (old : GALEC.UnitProfile.State Nat) :
    GALEC.UnitProfile.solveExecute (Solve.Algorithm.lower GALEC.unitBlock)
      0 1 (· + ·) .startup old = ⟨Value.fill scalar 0, Value.fill scalar 1⟩ := by
  rw [GALEC.UnitProfile.lower_correct]
  exact GALEC.UnitProfile.startup_initializes _ _ _ _

#audit axioms GALEC.lower_equation_correct
#audit axioms GALEC.lower_step_correct
#audit axioms GALEC.algorithm_step_correct
#audit axioms GALEC.unit_no_overflow
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
#audit axioms reads_period_rejected
#audit axioms changed_period
#audit axioms tensor_operation_order
#audit axioms initial_state_and_period

end Rumoca.EFMIChecks
