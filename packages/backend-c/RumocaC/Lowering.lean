import RumocaCore.SolveSemantics
import RumocaC.Execution
import RumocaC.PrinterProofs
import RumocaC.SyntaxProofs

/-! Solve-to-C contracts; independent of the compiler driver and source semantics. -/
noncomputable section
namespace Rumoca

namespace C
/-- Register elimination preserves the independently interpreted Solve RHS. -/
theorem lower_correct (m : Solve.Model source) (x : ℝ) :
    eval x (lower m).rhs = (m.rhs : ℝ) := by rw [rhs_correct, m.rhs_eq_one]; simp

/-- The finite-arithmetic lowering preserves the exact rounded step, including
its encoding, rather than merely satisfying a real-valued error bound. -/
theorem lower_binary64_correct (m : Solve.Model source) (x : Binary64.Value) :
    CExecution.eval x (lower m).step = some (m.advance x) := by
  rw [m.advance_correct]; exact CExecution.step_eval m x
end C

namespace CSyntax
/-- Rendering denotes the target program in the independent C text grammar. -/
theorem lower_correct (m : Solve.Model source) :
    Denotes (C.render (C.lower m)) (fromTarget (C.lower m)) := module_render (C.lower m)
end CSyntax

/-- Ideal arithmetic; binary64 rounding is covered in Real/Binary64.lean. -/
theorem C.ideal_run_correct (m : Solve.Model source) (x : ℝ) (n : Nat) :
    C.run (C.lower m) x n = x + n := by
  induction n generalizing x with
  | zero => simp [C.run]
  | succ n ih =>
    rw [C.run, C.step_correct, ih]
    simp [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]

end Rumoca
