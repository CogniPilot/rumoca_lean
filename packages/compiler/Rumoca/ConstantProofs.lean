import Rumoca.ConstantCompiler
import RumocaCore.Constant.Permutation
import ModelicaParser.Constant.Parser
import ModelicaParser.ActionsProofs

/-! Source-text binding and the instantaneous contract of the constant-rate
preparation API. Time stepping, finite C and FMU artifacts are separate
obligations, not consequences of these equation-equivalence theorems. -/
namespace Rumoca.ConstantCompiler
open ConstantProfile _root_.Parser Rumoca.Binary64

theorem Prepared.source_correct (a : Prepared source) :
    Lexes source.toList a.parsed.parsed.ast.tokens ∧
      EBNF.Accepts Generated.sourceGrammar (a.parsed.parsed.tokens.map Token.symbol) :=
  ⟨ParserActions.parsed_lexes actions a.parsed.parsed,
    ParserActions.parsed_in_ebnf a.parsed.parsed⟩

/-- Every declared state's derivative equals its stored IVP rate, and every
state initializes at `+0`. The lowering chain and initialization are preserved
in the prepared kernel. -/
theorem Prepared.equation_correct (a : Prepared source) (derivatives : String → Value) :
    a.parsed.parsed.ast.Solves derivatives ↔
      ∀ i, derivatives (a.parsed.parsed.ast.states.get i) = a.ivp.rateValues i := by
  rw [a.ivp_lowered]; exact a.parsed.parsed.ast.lowering_chain derivatives

theorem Prepared.initialization_correct (a : Prepared source) (values : String → Value) :
    a.parsed.parsed.ast.Initial values ↔
      ∀ i, values (a.parsed.parsed.ast.states.get i) = a.ivp.initial i := by
  rw [a.ivp_lowered]; exact a.parsed.parsed.ast.initialization_chain values

/-- Each per-state rate value is the round-to-nearest-even of the exact base-ten
content of its stored decimal literal. This is the exact-rounding obligation. -/
theorem Prepared.rate_exact (a : Prepared source) (i : Fin a.parsed.parsed.ast.states.length) :
    Scaled.RoundsNearestEven (a.ivp.rates i).scale (a.ivp.rates i).numerator
      (a.ivp.rateValues i) :=
  (a.ivp.rates i).rate_rounds

/-- Every successful source preparation binds the parsed tokens to that source
and preserves both the equation system and initialization in its stored IVP. -/
theorem prepare_correct (_checked : prepare source = .ok a) (derivatives values : String → Value) :
    ConstantProfile.parse source = .ok a.parsed.parsed ∧
      Lexes source.toList a.parsed.parsed.ast.tokens ∧
      EBNF.Accepts Generated.sourceGrammar (a.parsed.parsed.tokens.map Token.symbol) ∧
      (a.parsed.parsed.ast.Solves derivatives ↔
        ∀ i, derivatives (a.parsed.parsed.ast.states.get i) = a.ivp.rateValues i) ∧
      (a.parsed.parsed.ast.Initial values ↔
        ∀ i, values (a.parsed.parsed.ast.states.get i) = a.ivp.initial i) :=
  ⟨a.parsed.erases, a.source_correct.1, a.source_correct.2,
    a.equation_correct derivatives, a.initialization_correct values⟩

/-- The prepared IVP is invariant under permuting the source equations: the
written order of the `der` lines does not affect any state's rate. -/
theorem prepare_perm_invariant {m₁ m₂ : ConstantProfile.Model}
    (hstates : m₁.states = m₂.states) (hperm : m₁.equations.Perm m₂.equations)
    (h₁ : m₁.Resolved) (i : Fin m₁.states.length) (j : Fin m₂.states.length)
    (hij : i.val = j.val) :
    (m₁.lower).rateValues i = (m₂.lower).rateValues j :=
  Model.lower_rates_perm hstates hperm h₁ i j hij

end Rumoca.ConstantCompiler
