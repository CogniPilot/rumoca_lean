import Rumoca.Lowering
import RumocaCore.GALEC.Binary64
import RumocaCore.Solve.AlgorithmProofs

/-! DAE → Algorithm Code → executable Solve composition for the existing
unit derivative, with an explicit unit-step/zero-start sampling policy. The
continuous equation is not identified with its rounded implementation. -/
noncomputable section
namespace Rumoca.GALEC
open Rumoca.Tensor

def Model.execute (m : Model source) (method : Method) (state : Binary64.Value) : Binary64.Value :=
  (m.block.execute Binary64.positiveZero Binary64.one roundedAdd method
    (Value.fill scalar state))[0]

theorem startup_correct (m : Model source) (state : Binary64.Value) :
    m.execute .startup state = Binary64.positiveZero := by
  simp [Model.execute, m.profile, unitBlock, Block.execute, Block.body, Expr.eval]

theorem recalibrate_correct (m : Model source) (state : Binary64.Value) :
    m.execute .recalibrate state = state := by
  simp [Model.execute, m.profile, unitBlock, Block.execute, Block.body]

theorem doStep_correct (m : Model source) (state : Binary64.Value) :
    m.execute .doStep state = Binary64.advance state := by
  simp [Model.execute, m.profile, unitBlock, Block.execute, Block.body, Expr.eval,
    roundedAdd, Binary64.roundedAdd_one]

/-- The DAE licenses the unit derivative policy before GALEC projection. -/
theorem lower_equation_correct (dae : DAE.Model source) (dx : ℝ) :
    dae.Holds dx ↔ dx = 1 := by
  rw [Solve.lower_correct, Solve.Model.rhs_eq_one]
  simp

/-- The projected GALEC method preserves the existing finite Solve profile.
This comparison theorem does not route production code through a second DAE
lowering: its executable root is `Solve.Algorithm.lower m.block`. -/
theorem lower_step_correct (dae : DAE.Model source) (state : Binary64.Value) :
    (lower dae).execute .doStep state = (Solve.lower dae).advance state := by
  rw [doStep_correct, Solve.Model.advance_correct]

theorem algorithm_step_correct (m : Model source) (state : Binary64.Value) :
    ((Solve.Algorithm.lower m.block).execute Binary64.positiveZero Binary64.one
      roundedAdd .doStep (Value.fill scalar state))[0] = m.execute .doStep state := by
  rw [Solve.Algorithm.lower_correct]
  rfl

def Model.run (m : Model source) (state : Binary64.Value) : Nat → Binary64.Value
  | 0 => state
  | n + 1 => m.run (m.execute .doStep state) n

theorem run_correct (m : Model source) (state : Binary64.Value) (n : Nat) :
    m.run state n = Binary64.run state n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp only [Model.run, Binary64.run, doStep_correct, ih]

/-- The single admitted addition cannot overflow for any finite input state.
No NaN/Infinity or error-signal branch is being silently assumed away for it. -/
theorem unit_no_overflow (state : Binary64.Value) :
    -(Binary64.maxUnits + 2 ^ 2044 : Int) < Binary64.units state + Binary64.oneUnits ∧
    Binary64.units state + Binary64.oneUnits < (Binary64.maxUnits + 2 ^ 2044 : Int) :=
  Binary64.advance_no_overflow state

end Rumoca.GALEC
