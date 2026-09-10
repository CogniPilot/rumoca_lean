import ProofAudit.Audit
import RumocaCore.Tensor.Matrix
import RumocaCore.Driven.Lowering

namespace Rumoca.TensorChecks
open Rumoca.Tensor

/-- Equal storage volume cannot erase rank or permit a tensor-register mixup. -/
theorem equal_volume_different_shapes :
    (matrixShape 2 3).volume = (Shape.mk [6]).volume ∧ matrixShape 2 3 ≠ ⟨[6]⟩ := by
  decide +kernel

example : True := by
  fail_if_success
    have bad : Value Nat (matrixShape 2 3) := Value.fill ⟨[6]⟩ 0
  trivial

example : True := by
  fail_if_success
    have bad : Solve.Tensor.Ref [matrixShape 2 3] ⟨[6]⟩ := .here
  trivial

/-- The storage bridge agrees with mathlib's row/column ordering, including
an off-diagonal entry that detects accidental transposition. -/
theorem matrix_storage_order :
    (Value.ofMatrix (Matrix.of fun (i : Fin 2) (j : Fin 3) => 10 * i.val + j.val)).data.toArray =
      #[0, 1, 2, 10, 11, 12] := by decide +kernel

theorem empty_matrix_roundtrip (m : Matrix (Fin 0) (Fin 3) Nat) :
    (Value.ofMatrix m).toMatrix = m := Value.toMatrix_ofMatrix m

/-- Initialization cannot be silently changed when the differential equation
would otherwise remain correct. -/
theorem wrong_initialization_rejected (m : Driven.DAE.Model source)
    (input derivative : Value ℝ scalar) :
    ¬ m.Initial (Driven.singleton 1) input derivative := by
  rw [Driven.Solved.lower_initial]
  change ¬ Driven.singleton (1 : ℝ) = Driven.singleton 0
  intro h
  have h := Driven.singleton_injective h
  norm_num at h

#audit axioms equal_volume_different_shapes
#audit axioms matrix_storage_order
#audit axioms empty_matrix_roundtrip
#audit axioms wrong_initialization_rejected

end Rumoca.TensorChecks
