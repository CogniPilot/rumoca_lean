import Rumoca.Source
import RumocaCore.Initialization.Real
import RumocaCore.Solve.FMI3
import RumocaCore.GALEC.UnitProfile

/-! Initialization correspondence for the actually admitted unmodified Real
declaration. The source is underdetermined; the checked compiler plan completes
it with the Real fallback and records both notices. New modifiers/bindings still
need source parsing and target/artifact admission before becoming production. -/
noncomputable section
namespace Rumoca

def Source.initializationSettings (_ : AST.Model) : Initialization.Settings Nat :=
  ⟨none, none, false⟩

def Source.Initializes (source : AST.Model) (t₀ : ℝ) (x : ℝ → ℝ) : Prop :=
  AST.Resolved source ∧ Initialization.SourceSolution
    ((initializationSettings source).map (fun n : Nat => (n : ℝ))) t₀ x

/-- No source initial equation is invented for the unmodified declaration. -/
theorem Source.initializes_iff (source : AST.Model) (t₀ : ℝ) (x : ℝ → ℝ) :
    Initializes source t₀ x ↔ Solves source x := by
  simp [Initializes, Solves, initializationSettings, Initialization.Settings.map,
    Initialization.SourceSolution]

theorem Flat.Model.initialization_matches (m : Flat.Model source) :
    m.initialization = Source.initializationSettings source := m.initialization_source

theorem DAE.Model.initialization_matches (m : DAE.Model source) :
    m.initialization = Source.initializationSettings source :=
  m.initialization_source.trans m.flat.initialization_matches

/-- This is the actual stored plan's checked decision, interpreted in Real;
there is no separately supplied initial value or supplied lowering result. -/
theorem Solve.Model.initialization_checked_real (m : Solve.Model source) :
    Initialization.prepare
      ((Source.initializationSettings source).map (fun n : Nat => (n : ℝ))) 0 =
      .ok (m.initial.map (fun n : Nat => (n : ℝ))) := by
  rw [← m.dae.initialization_matches]
  have mapped := Initialization.prepare_map (fun n : Nat => (n : ℝ)) m.dae.initialization 0
  rw [m.initial_checked] at mapped
  simpa only [Nat.cast_zero, Except.map] using mapped

theorem Solve.Model.initialization_correct (m : Solve.Model source) (t₀ : ℝ) :
    Source.Initializes source t₀ (Initialization.trajectory t₀ (m.initial.initial : ℝ)) ∧
    Initialization.Notice.fallbackUsed ∈ m.initial.notices ∧
    Initialization.Notice.unfixedStartSelected ∈ m.initial.notices := by
  refine ⟨⟨m.dae.flat.resolved, ?_⟩, ?_⟩
  · exact Initialization.prepare_sound _ _ m.initialization_checked_real t₀
  · rw [m.initial_default]
    simp

theorem Solve.Model.initialized_solution_unique (m : Solve.Model source) (t₀ : ℝ)
    (x : ℝ → ℝ) (solution : Source.Initializes source t₀ x)
    (initial : x t₀ = (m.initial.initial : ℝ)) :
    x = Initialization.trajectory t₀ (m.initial.initial : ℝ) :=
  Initialization.completed_solution_unique _ (m.initial.map (fun n : Nat => (n : ℝ)))
    x t₀ solution.2 initial

/-- Existing tensor IVP initialization agrees with the prepared default plan.
The adapter still needs to execute and certify the actual initialization write. -/
theorem Solve.FMI3Model.initialization_matches (m : Solve.FMI3Model source)
    (ops : Tensor.ScalarOps ℝ) :
    m.problem.initial ops 0 1 = Tensor.Value.fill _ (m.solve.initial.initial : ℝ) := by
  rw [m.solve.initial_default]
  change Tensor.Value.fill _ (0 : ℝ) = Tensor.Value.fill _ ((0 : Nat) : ℝ)
  rw [Nat.cast_zero]

/-- The GALEC path selects the same default from the same DAE problem. -/
theorem GALEC.initialization_matches (dae : DAE.Model source)
    (state : UnitProfile.State ℝ) :
    (UnitProfile.execute (lower dae).block 0 1 (· + ·) .startup state).x =
      Tensor.Value.fill _ ((Solve.lower dae).initial.initial : ℝ) := by
  rw [(Solve.lower dae).initial_default]
  change Tensor.Value.fill _ (0 : ℝ) = Tensor.Value.fill _ ((0 : Nat) : ℝ)
  rw [Nat.cast_zero]

end Rumoca
