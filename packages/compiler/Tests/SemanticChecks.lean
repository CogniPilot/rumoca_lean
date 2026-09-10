import ProofAudit.Audit
import Rumoca

/-! Checked regressions for counterexamples found in the semantic review. -/
noncomputable section
open Rumoca Binary64
namespace Rumoca.SemanticChecks

set_option maxRecDepth 10000

theorem signed_zero_additions_differ :
    roundedAdd negativeZero negativeZero ≠ roundedAdd positiveZero positiveZero := by
  rw [roundedAdd_negative_zero, roundedAdd_positive_zero]
  decide +kernel

theorem missing_parameter_rejected :
    ¬ CStatements.WellScoped (⟨.arg, .arg, .arg⟩ : CSyntax.Program) := by
  simp [CStatements.WellScoped, CStatements.Scoped]

theorem unsigned_zero_wraps : (CStatements.decrement 0).val = 2 ^ 64 - 1 := by
  decide +kernel

theorem infinity_excluded :
    ¬ (BitVec.ofNat 64 0x7ff0000000000000).toNat % signPlace < magnitudeCount := by
  decide +kernel

/-- The global error inequality alone admits stagnation everywhere. The full
behavioral contract rejects that faulty implementation already at x=0.5. -/
theorem frozen_sampler_rejected (m : Solve.Model source) :
    ¬ (CStatements.machine (CExecution.program m)).Behaves
      (.entry .sample half 1) (.terminates half) := by
  intro h
  have he := (CStatements.behaviors_correct m .sample half 1).mp h
  have he := congrArg value (Transition.Observation.terminates.inj he)
  rw [CStatements.result_correct] at he
  change value half = value (advance half) at he
  rw [value_half, advance_half] at he
  norm_num at he

#audit axioms signed_zero_additions_differ
#audit axioms missing_parameter_rejected
#audit axioms unsigned_zero_wraps
#audit axioms infinity_excluded
#audit axioms frozen_sampler_rejected

/-- A numerical policy must not accept the wrong equation even if the target
would still implement a perfectly terminating add-one loop. -/
theorem wrong_equation_rejected :
    ¬ Profile.Behavior (fun dx => dx = (0 : ℝ)) f x n b := by
  rintro ⟨ha, _⟩
  have h := (ha 0).mp rfl
  norm_num at h

/-- Requiring only that derivative 1 is possible would also license an
underdetermined model. The complete solution-set condition rejects it. -/
theorem underdetermined_equation_rejected :
    ¬ Profile.Behavior (fun _ => True) f x n b := by
  rintro ⟨ha, _⟩
  have h := (ha 0).mp trivial
  norm_num at h

/-- The source semantics is inhabited for every resolved model and input.
This is a positive control alongside rejection of wrong/stuck executions. -/
theorem source_behavior_exists (h : AST.Resolved m) (f : Profile.Function)
    (x : Value) (n : Nat) : ∃ b, Source.SampledBehavior m f x n b :=
  ⟨_, (Source.sampled_behavior_iff h).mpr rfl⟩

#audit axioms wrong_equation_rejected
#audit axioms underdetermined_equation_rejected
#audit axioms source_behavior_exists
end Rumoca.SemanticChecks
