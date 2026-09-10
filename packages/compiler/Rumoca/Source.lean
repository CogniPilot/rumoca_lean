import ModelicaParser.AST
import RumocaCore.Profile
import Mathlib.Analysis.Calculus.Deriv.Add

open _root_.Parser

/-! Authored source and numerical-profile semantics. This module's transitive
imports contain no backend, compiler driver, or target execution definition. -/
noncomputable section
namespace Rumoca.Source
open Binary64 Transition

def Equation (m : AST.Model) (derivatives : String → ℝ) : Prop :=
  derivatives m.derivativeName = 1

def Solves (m : AST.Model) (x : ℝ → ℝ) : Prop :=
  AST.Resolved m ∧ ∀ t, HasDerivAt x 1 t

def trajectory (x₀ : ℝ) (t : ℝ) : ℝ := x₀ + t

theorem trajectory_derivative (x₀ t : ℝ) : HasDerivAt (trajectory x₀) 1 t := by
  simpa [trajectory] using (hasDerivAt_id t).const_add x₀

theorem trajectory_solves (m : AST.Model) (h : AST.Resolved m) (x₀ : ℝ) :
    Solves m (trajectory x₀) := ⟨h, trajectory_derivative x₀⟩

abbrev RoundedSamples := Profile.RoundedSamples
abbrev profileResult := Profile.result

theorem rounded_samples (x : Value) (n : Nat) : RoundedSamples x n (run x n) :=
  Profile.rounded_samples x n

theorem rounded_samples_unique (h : RoundedSamples x n y) : y = run x n :=
  Profile.rounded_samples_unique h

/-- The source equation must license the numerical policy. Name resolution is
required separately; constant derivative assignments cannot resolve a name. -/
def SampledBehavior (m : AST.Model) (f : Profile.Function) (x : Value) (n : Nat)
    (b : Observation Value) : Prop :=
  AST.Resolved m ∧ Profile.Behavior (fun dx => Equation m (fun _ => dx)) f x n b

theorem sampled_behavior_iff (h : AST.Resolved m) :
    SampledBehavior m f x n b ↔ b = .terminates (profileResult f x n) := by
  rw [SampledBehavior, and_iff_right h]
  exact Profile.behavior_iff (fun _ => Iff.rfl)

end Rumoca.Source
