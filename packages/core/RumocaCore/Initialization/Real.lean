import RumocaCore.Initialization.Scalar
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue

/-! MLS 3.7 §§4.4.2.1, 4.9 and 8.6 for the unit-derivative profile.
Source constraints and the tool's completion of an underdetermined initial
problem are separate. These definitions do not admit new source syntax. -/
noncomputable section
namespace Rumoca.Initialization

/-- An ordinary binding is a simulation equation; an unfixed start is not an
initial equation. Missing Real start values use the unbounded-type fallback 0. -/
def SourceSolution (settings : Settings ℝ) (t₀ : ℝ) (x : ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt x 1 t) ∧
  (∀ value, settings.binding = some value → ∀ t, x t = value) ∧
  (settings.fixed = true → x t₀ = settings.startValue 0)

def trajectory (t₀ initial t : ℝ) : ℝ := initial + (t - t₀)

theorem trajectory_derivative (t₀ initial t : ℝ) :
    HasDerivAt (trajectory t₀ initial) 1 t := by
  change HasDerivAt (fun s : ℝ => initial + (s - t₀)) 1 t
  exact ((hasDerivAt_id t).sub_const t₀).const_add initial

theorem trajectory_initial (t₀ initial : ℝ) : trajectory t₀ initial t₀ = initial := by
  simp [trajectory]

theorem constant_binding_inconsistent (settings : Settings ℝ) (t₀ value : ℝ)
    (bound : settings.binding = some value) : ¬ ∃ x, SourceSolution settings t₀ x := by
  rintro ⟨x, derivative, binding, _⟩
  have same : x = fun _ => value := funext (binding value bound)
  have zero : HasDerivAt x 0 t₀ := same ▸ hasDerivAt_const t₀ value
  have impossible : (1 : ℝ) = 0 := (derivative t₀).unique zero
  norm_num at impossible

theorem prepare_sound (settings : Settings ℝ) (plan : Plan ℝ)
    (accepted : prepare settings 0 = .ok plan) (t₀ : ℝ) :
    SourceSolution settings t₀ (trajectory t₀ plan.initial) := by
  refine ⟨trajectory_derivative t₀ plan.initial, ?_, ?_⟩
  · intro value binding
    rw [prepare_no_binding accepted] at binding
    contradiction
  · intro _
    rw [trajectory_initial, prepare_initial accepted]

theorem prepare_complete (settings : Settings ℝ) (t₀ : ℝ)
    (possible : ∃ x, SourceSolution settings t₀ x) :
    ∃ plan, prepare settings 0 = .ok plan := by
  cases binding : settings.binding with
  | none => simp [prepare, binding]
  | some value => exact False.elim (constant_binding_inconsistent settings t₀ value binding possible)

/-- The selected initial equation, together with the ODE, has a unique real
trajectory for every initial time. This is stronger than checking a sample. -/
theorem completed_solution_unique (settings : Settings ℝ) (plan : Plan ℝ)
    (x : ℝ → ℝ) (t₀ : ℝ) (solution : SourceSolution settings t₀ x)
    (initial : x t₀ = plan.initial) : x = trajectory t₀ plan.initial := by
  have derivative (t : ℝ) : HasDerivAt (fun t => x t - t) 0 t := by
    simpa only [sub_self] using (solution.1 t).sub (hasDerivAt_id t)
  funext t
  have constant := is_const_of_deriv_eq_zero (fun t => (derivative t).differentiableAt)
    (fun t => (derivative t).deriv) t t₀
  rw [initial] at constant
  dsimp [trajectory]
  linarith

theorem unfixed_start_is_free (start : Option ℝ) (t₀ initial : ℝ) :
    SourceSolution ⟨none, start, false⟩ t₀ (trajectory t₀ initial) := by
  exact ⟨trajectory_derivative t₀ initial, by simp, by simp⟩

end Rumoca.Initialization
