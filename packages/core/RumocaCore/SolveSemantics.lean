import RumocaCore.IR
import RumocaCore.Real.Binary64

/-! Target-independent finite execution of Solve IR for the admitted sampling profile. -/
noncomputable section
namespace Rumoca.Solve

/-- The finite-arithmetic interpretation evaluates the actual register program. -/
def Model.realRhs (m : Model source) : Binary64.Value :=
  evalWith Binary64.one m.derivative Fin.elim0

theorem Model.realRhs_eq_one (m : Model source) : m.realRhs = Binary64.one := by
  simp [Model.realRhs, m.derivative_source, unitDerivative, evalWith]

/-- Sampling policy for this profile: unit time steps, nearest-even arithmetic. -/
def Model.advance (m : Model source) (x : Binary64.Value) : Binary64.Value :=
  Binary64.round (Binary64.units x + Binary64.units m.realRhs)

def Model.run (m : Model source) (x : Binary64.Value) : Nat → Binary64.Value
  | 0 => x
  | n + 1 => m.run (m.advance x) n

theorem Model.advance_correct (m : Model source) (x : Binary64.Value) :
    m.advance x = Binary64.advance x := by
  simp only [Model.advance, m.realRhs_eq_one, Binary64.units_one, Binary64.advance]

theorem Model.run_correct (m : Model source) (x : Binary64.Value) (n : Nat) :
    m.run x n = Binary64.run x n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [Model.run, Model.advance_correct, ih, Binary64.run]
end Rumoca.Solve
