import Rumoca.Semantics
import RumocaC.Lowering

/-! Public contracts for each pass. Logical equation equivalence ends at Solve;
choosing finite arithmetic is a numerical interpretation, not exact real equality. -/
noncomputable section
namespace Rumoca

namespace Flat
/-- Name resolution and flattening preserve the written source equation. -/
theorem lower_correct (source : AST.Model) (h : AST.Resolved source) (d : String → ℝ) :
    Source.Equation source d ↔ (lower source h).Holds (d source.state) :=
  flatten_correct (lower source h) d
end Flat

namespace DAE
/-- Forming a residual preserves precisely the solutions of the flat equation. -/
theorem lower_correct (m : Flat.Model source) (dx : ℝ) :
    m.Holds dx ↔ (lower m).Holds dx := (dae_correct (lower m) dx).symm
end DAE

namespace Solve
/-- Solving the residual preserves precisely its derivative solutions. -/
theorem lower_correct (m : DAE.Model source) (dx : ℝ) :
    m.Holds dx ↔ dx = ((lower m).rhs : ℝ) := solve_correct (lower m) dx

end Solve

/-- Explicit composition of the public per-pass real equation contracts. -/
theorem lowering_chain_correct (source : AST.Model) (h : AST.Resolved source)
    (d : String → ℝ) (x : ℝ) :
    Source.Equation source d ↔ d source.state =
      C.eval x (C.lower (Solve.lower (DAE.lower (Flat.lower source h)))).rhs := by
  rw [Flat.lower_correct source h, DAE.lower_correct, Solve.lower_correct, C.lower_correct]

end Rumoca
