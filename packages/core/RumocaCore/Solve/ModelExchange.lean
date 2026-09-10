import RumocaCore.SolveSemantics

/-! Model/solver separation for the first ME-within-CS core. These are internal
semantic interfaces, not implementations of the FMI ABI or lifecycle. Time is
an exact count of unit steps from an externally supplied origin. FMI Float64
communication times, statuses and instance memory require separate contracts. -/
noncomputable section
namespace Rumoca
open Binary64

namespace ModelExchange

/-- Model state, owned by the equation kernel rather than the solver. -/
structure State where
  x : Value

def setContinuousState (_ : State) (x : Value) : State := ⟨x⟩
def getContinuousState (s : State) : Value := s.x

/-- The model exposes the actual solved derivative and does not advance time. -/
def derivative (m : Solve.Model source) (_ : State) : Value := m.realRhs

theorem get_set (s : State) (x : Value) :
    getContinuousState (setContinuousState s x) = x := rfl

theorem derivative_correct (m : Solve.Model source) (s : State) :
    derivative m s = one := m.realRhs_eq_one

end ModelExchange

namespace UnitSolver

/-- The internal solver consumes the ME kernel. With step size exactly one,
Euler's update needs one rounded addition and no floating multiplication. -/
def step (m : Solve.Model source) (s : ModelExchange.State) : ModelExchange.State :=
  ⟨round (units s.x + units (ModelExchange.derivative m s))⟩

theorem step_correct (m : Solve.Model source) (s : ModelExchange.State) :
    (step m s).x = m.advance s.x := rfl

theorem step_no_overflow (m : Solve.Model source) (s : ModelExchange.State) :
    -(maxUnits + 2 ^ 2044 : Int) < units s.x + units (ModelExchange.derivative m s) ∧
    units s.x + units (ModelExchange.derivative m s) < (maxUnits + 2 ^ 2044 : Int) := by
  rw [ModelExchange.derivative_correct, units_one]
  exact advance_no_overflow s.x

end UnitSolver

namespace CoSimulation

/-- CS owns the solver's progress and contains the shared ME model state.
This exact counter is not an FMI Float64 communication-time representation. -/
structure State where
  model : ModelExchange.State
  completedSteps : Nat

def doStep (m : Solve.Model source) (s : State) : State :=
  ⟨UnitSolver.step m s.model, s.completedSteps + 1⟩

def run (m : Solve.Model source) (s : State) : Nat → State
  | 0 => s
  | n + 1 => run m (doStep m s) n

/-- Repeated CS advancement uses precisely the previously verified finite
Solve execution. The derivative is evaluated through the shared ME kernel. -/
theorem run_model_correct (m : Solve.Model source) (s : State) (n : Nat) :
    (run m s n).model.x = m.run s.model.x n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [run, ih, Solve.Model.run]
    rfl

theorem run_progress (m : Solve.Model source) (s : State) (n : Nat) :
    (run m s n).completedSteps = s.completedSteps + n := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => simp only [run, ih, doStep]; omega

end CoSimulation
end Rumoca
