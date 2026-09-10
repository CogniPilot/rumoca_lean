import ProofAudit.Audit
import Rumoca.EFMIManifestProofs
import Rumoca.EFMIArchiveProofs

#audit axioms Rumoca.EFMI.manifests_correct
#audit axioms Rumoca.EFMI.manifests_correct_of_documents
#audit axioms Rumoca.EFMI.ManifestContract.source_name
#audit axioms Rumoca.EFMI.archive_correct
#audit axioms Rumoca.EFMI.ArchiveContract.code_members
#audit axioms Rumoca.EFMI.ArchiveContract.schema_members
#audit axioms Rumoca.EFMI.ArchiveContract.roster
#audit axioms Rumoca.EFMI.archive_code_correct
#audit axioms Rumoca.EFMI.efmu_archive_correct
#audit axioms Rumoca.EFMI.compile_archive_verified

namespace Rumoca.EFMIChecks
open Rumoca.Tensor

theorem mismatched_reference :
    ¬ GALEC.Syntax.Resolved { GALEC.Syntax.unit with stepRead := "samplePeriod" } := by
  decide +kernel

theorem aliased_declarations :
    ¬ GALEC.Syntax.Resolved { GALEC.Syntax.unit with clock := "x" } := by
  decide +kernel

theorem changed_period :
    ¬ EFMI.Denotes GALEC.Syntax.unit { GALEC.unitBlock with startupPeriod := .zero } := by
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
#audit axioms EFMI.compile_production_verified
#audit axioms mismatched_reference
#audit axioms aliased_declarations
#audit axioms changed_period
#audit axioms tensor_operation_order
#audit axioms initial_state_and_period

end Rumoca.EFMIChecks
