import RumocaCore.SolveSemantics
import RumocaCore.Initialization.Real

/-! Numerical error at a reported time. The exact solver duration and the
communication clock are separate quantities; later call traces must establish
their relationship rather than silently identify them. -/
noncomputable section
namespace Rumoca.Solve

theorem Model.run_error_at_time (model : Model source) (x : Binary64.Value)
    (n : Nat) (start reported : ℝ) :
    |Binary64.value (model.run x n) - Initialization.trajectory start (Binary64.value x) reported| ≤
      (n : ℝ) + |reported - (start + (n : ℝ))| := by
  rw [model.run_correct, Initialization.trajectory]
  have decompose : Binary64.value (Binary64.run x n) - (Binary64.value x + (reported - start)) =
      (Binary64.value (Binary64.run x n) - (Binary64.value x + (n : ℝ))) +
        ((start + (n : ℝ)) - reported) := by ring
  rw [decompose]
  exact (abs_add_le _ _).trans (add_le_add (Binary64.run_error x n) (le_of_eq (abs_sub_comm _ _)))

theorem Model.run_exact_at_time (model : Model source) (x : Binary64.Value)
    (n : Nat) (start reported : ℝ)
    (samples : ∀ k ≤ n, ∃ y : Binary64.Value, Binary64.value y = Binary64.value x + k)
    (clock : reported = start + (n : ℝ)) :
    Binary64.value (model.run x n) = Initialization.trajectory start (Binary64.value x) reported := by
  rw [model.run_correct, Binary64.run_exact x n samples, Initialization.trajectory, clock]
  ring

/-- Repeated helper calls compose without placing a machine-width limit on
the ghost cumulative duration. Each individual native count has its own bound. -/
theorem Model.run_add (model : Model source) (x : Binary64.Value) (n m : Nat) :
    model.run x (n + m) = model.run (model.run x n) m := by
  induction n generalizing x with
  | zero => simp only [Nat.zero_add, Model.run]
  | succ n ih => simpa only [Nat.succ_add, Model.run] using ih (model.advance x)

end Rumoca.Solve
end
