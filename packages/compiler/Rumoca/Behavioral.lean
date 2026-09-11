import RumocaC.Statements
import Rumoca.Lowering
import RumocaCore.Real.Encoding
import RumocaCore.Solve.ModelExchange
import Mathlib.Analysis.Calculus.MeanValue

/-! Whole-compiler behavioral correctness for the admitted numerical profile.
The source ODE is real-valued. Its numerical profile has independent relational
nearest-even sampling semantics; exact behavior preservation is proved against
that profile, and approximation to the unique real solution is stated separately. -/
noncomputable section
namespace Rumoca
open Binary64 Transition

namespace Source

/-- The admitted initial-value problem has exactly one real solution. -/
theorem solution_unique (h : Solves m f) (hi : f 0 = x₀) (t : ℝ) :
    f t = trajectory x₀ t := by
  have hd (t : ℝ) : HasDerivAt (fun t => f t - t) 0 t := by
    simpa only [sub_self] using (h.2 t).sub (hasDerivAt_id t)
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0
  simp only [sub_zero, hi] at hc
  simp only [trajectory]
  linarith

end Source

/-- Interpret each real IR with the same, explicitly restricted numerical
policy. The policy's applicability condition is transported by equation
equivalence; the representations do not share an execution definition. -/
def Flat.SampledBehavior (m : Flat.Model source) := Profile.Behavior m.Holds
def DAE.SampledBehavior (m : DAE.Model source) := Profile.Behavior m.Holds
def Solve.SampledBehavior (m : Solve.Model source) :=
  Profile.Behavior (fun dx => dx = (m.rhs : ℝ))

theorem Flat.behavior_correct (m : Flat.Model source) :
    Source.SampledBehavior source f x n b ↔ Flat.SampledBehavior m f x n b := by
  rw [Source.SampledBehavior, and_iff_right m.resolved]
  exact Profile.behavior_congr (fun dx => flatten_correct m (fun _ => dx))

theorem DAE.behavior_correct (m : DAE.Model source) :
    Flat.SampledBehavior m.flat f x n b ↔ DAE.SampledBehavior m f x n b :=
  Profile.behavior_congr (fun dx => (dae_correct m dx).symm)

theorem Solve.behavior_correct (m : Solve.Model source) :
    DAE.SampledBehavior m.dae f x n b ↔ Solve.SampledBehavior m f x n b :=
  Profile.behavior_congr (fun dx => solve_correct m dx)

/-- Solve execution realizes the independent relational source sampling policy. -/
theorem Solve.lower_samples_correct (m : Solve.Model source) (x : Value) (n : Nat) :
    Source.RoundedSamples x n y ↔ y = m.run x n := by
  rw [m.run_correct]
  exact ⟨Source.rounded_samples_unique, fun h => h ▸ Source.rounded_samples x n⟩

theorem CStatements.result_correct (m : Solve.Model source) (f : CStatements.Function)
    (x : Value) (n : CStatements.Counter) :
    CStatements.result m f x n = Source.profileResult f x n.val := by
  cases f
  · exact m.realRhs_eq_one
  · exact m.advance_correct x
  · exact m.run_correct x n.val

/-- This edge relates statement execution to Solve's numerical semantics.
Source/Flat/DAE semantics enter only when the preceding pass proofs compose. -/
theorem CStatements.solve_behavior_correct (m : Solve.Model source) (f : Profile.Function)
    (x : Value) (n : CStatements.Counter) (b : Observation Value) :
    (CStatements.machine (CExecution.program m)).Behaves (.entry f x n) b ↔
      Solve.SampledBehavior m f x n.val b := by
  have ha : Profile.AdmitsUnit (fun dx => dx = (m.rhs : ℝ)) := by
    intro dx
    rw [m.rhs_eq_one, Nat.cast_one]
  rw [CStatements.behaviors_correct, Solve.SampledBehavior, Profile.behavior_iff ha,
    CStatements.result_correct]

/-- Exact forward and backward preservation of every observable behavior,
including the absence of stuck and diverging target executions. -/
theorem CStatements.lower_behavior_correct (m : Solve.Model source) (f : Profile.Function)
    (x : Value) (n : CStatements.Counter) (b : Observation Value) :
    (CStatements.machine (CExecution.program m)).Behaves (.entry f x n) b ↔
      Source.SampledBehavior source f x n.val b := by
  exact (CStatements.solve_behavior_correct m f x n b).trans
    ((Solve.behavior_correct m).symm.trans
      ((DAE.behavior_correct m.dae).symm.trans (Flat.behavior_correct m.dae.flat).symm))

/-- Instantiation of the behavioral composition with every actual lowering
function in the driver. This is still the frozen unit policy, not a general
simulation theorem for arbitrary numerical methods or future IR constructors. -/
theorem lowering_chain_behavior_correct (context : Provenance.Context source) (h : AST.Resolved source)
    (f : Profile.Function) (x : Value) (n : CStatements.Counter) (b : Observation Value) :
    (CStatements.machine (CExecution.program (Solve.lower (DAE.lower (Flat.lower context h))))).Behaves
      (.entry f x n) b ↔ Source.SampledBehavior source f x n.val b :=
  CStatements.lower_behavior_correct _ f x n b

/-- The scalar RHS export realizes the shared ME derivative kernel. This is
an internal model contract, not a claim about an FMI function or instance. -/
theorem CStatements.model_exchange_correct (m : Solve.Model source)
    (x : Value) (n : CStatements.Counter) (b : Observation Value) :
    (CStatements.machine (CExecution.program m)).Behaves (.entry .rhs x n) b ↔
      b = .terminates (ModelExchange.derivative m ⟨x⟩) :=
  CStatements.behaviors_correct m .rhs x n

/-- The scalar sample export realizes CS's internal repeated solver over the
nested ME state. FMI lifecycle, Float64 time and instance-memory behavior are
not asserted by this theorem. -/
theorem CStatements.co_simulation_correct (m : Solve.Model source)
    (x : Value) (n : CStatements.Counter) (b : Observation Value) :
    (CStatements.machine (CExecution.program m)).Behaves (.entry .sample x n) b ↔
      b = .terminates ((CoSimulation.run m ⟨⟨x⟩, 0⟩ n.val).model.x) := by
  rw [CoSimulation.run_model_correct]
  exact CStatements.behaviors_correct m .sample x n

/-- Sample accuracy against ANY solution of the source initial-value problem,
not merely a hand-picked reference trajectory. -/
theorem CStatements.real_refinement (m : Solve.Model source) (x : Value)
    (n : CStatements.Counter) (hf : Source.Solves source f) (hi : f 0 = value x)
    (hb : (CStatements.machine (CExecution.program m)).Behaves
      (.entry .sample x n) (.terminates y)) :
    |value y - f n.val| ≤ n.val := by
  have he := (CStatements.behaviors_correct m .sample x n).mp hb
  have hy := Observation.terminates.inj he
  rw [hy, CStatements.result_correct, Source.profileResult,
    Source.solution_unique hf hi, Source.trajectory]
  exact run_error x n.val

end Rumoca
