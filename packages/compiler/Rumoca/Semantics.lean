import RumocaC.Lowering
import Rumoca.Compiler
import ModelicaParser.ParserProofs
import Rumoca.Source

open _root_.Parser

/-! Authored reference semantics for the MLS 3.7 slice. The MLS is prose, so
the correspondence to that prose is a review obligation, not a Lean theorem. -/
noncomputable section
namespace Rumoca

def Flat.Expr.eval (derivatives : Fin 1 → ℝ) : Flat.Expr → ℝ
  | .der i => derivatives i
  | .one => 1

def Flat.Model.Holds (m : Flat.Model source) (dx : ℝ) : Prop :=
  m.lhs.eval (fun _ => dx) = m.rhs.eval (fun _ => dx)

theorem flatten_correct (m : Flat.Model source) (d : String → ℝ) :
    Source.Equation source d ↔ m.Holds (d source.state) := by
  simp [Source.Equation, Flat.Model.Holds, m.lhs_source, m.rhs_source,
    Flat.Expr.eval, m.resolved.derivative_resolves]

def DAE.Expr.eval (derivatives : Fin 1 → ℝ) : DAE.Expr → ℝ
  | .derivative i => derivatives i
  | .one => 1
  | .sub a b => a.eval derivatives - b.eval derivatives

theorem lowerExpr_correct (e : Flat.Expr) (d : Fin 1 → ℝ) :
    (DAE.lowerExpr e).eval d = e.eval d := by cases e <;> rfl

def DAE.Model.Holds (m : DAE.Model source) (dx : ℝ) : Prop :=
  m.residual.eval (fun _ => dx) = 0

theorem dae_correct (m : DAE.Model source) (dx : ℝ) :
    m.Holds dx ↔ m.flat.Holds dx := by
  simp [DAE.Model.Holds, m.residual_source, DAE.Expr.eval, lowerExpr_correct,
    Flat.Model.Holds, sub_eq_zero]

theorem solve_correct (m : Solve.Model source) (dx : ℝ) :
    m.dae.Holds dx ↔ dx = (m.rhs : ℝ) := by
  rw [dae_correct, m.rhs_eq_one]
  simp [Flat.Model.Holds, m.dae.flat.lhs_source, m.dae.flat.rhs_source, Flat.Expr.eval]

/-- Source equation → Flat → DAE → Solve → the independently interpreted C AST. -/
theorem compiler_correct (m : Solve.Model source) (d : String → ℝ) (input : ℝ) :
    Source.Equation source d ↔ d source.state = C.eval input (C.lower m).rhs := by
  rw [flatten_correct m.dae.flat, ← dae_correct m.dae, solve_correct m,
    C.rhs_correct, m.rhs_eq_one]
  simp

theorem ideal_samples_refine_solution (m : Solve.Model source) (x₀ : ℝ) (n : Nat) :
    Source.Solves source (Source.trajectory x₀) ∧
    C.run (C.lower m) x₀ n = Source.trajectory x₀ (n : ℝ) := by
  constructor
  · exact Source.trajectory_solves source m.dae.flat.resolved _
  · exact C.ideal_run_correct m x₀ n

/-- Composition for the actual source-bound product returned by `compile`.
Lexing, parsing, source name resolution, the ODE, and target execution are all
related in one statement, for every successful compilation and every sample. -/
theorem ideal_end_to_end (a : Artifact text) (x₀ : ℝ) (n : Nat) :
    Lexes text.source.toList a.parsed.ast.tokens ∧
    Source.Solves a.parsed.ast (Source.trajectory x₀) ∧
    C.run a.target x₀ n = Source.trajectory x₀ (n : ℝ) :=
  ⟨parsed_lexes a.parsed, ideal_samples_refine_solution a.solve x₀ n⟩

/-- Layout only. Verified.lean connects the emitted text to the authored C
grammar, operational semantics and binary64 rounding contract. -/
theorem emitted_text_is_unit (a : Artifact text) (linkage : C.Linkage := .external) :
    a.cSource linkage = C.unitText linkage := C.emission_is_unit a.solve linkage

end Rumoca
