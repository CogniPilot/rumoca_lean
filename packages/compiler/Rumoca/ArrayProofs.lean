import Rumoca.ArrayCompiler
import RumocaCore.Array.Lowering
import ModelicaParser.ActionsProofs

/-! Source-text binding and the complete instantaneous Real contract of the
array preparation API. Time stepping, finite C and FMU artifacts are separate
obligations; they are not consequences of this equation-equivalence theorem. -/
noncomputable section
namespace Rumoca.ArrayCompiler
open ArrayProfile Tensor _root_.Parser

theorem Prepared.source_correct (a : Prepared source) :
    Lexes source.toList a.parsed.parsed.ast.tokens ∧
      EBNF.Accepts Generated.sourceGrammar (a.parsed.parsed.tokens.map Token.symbol) :=
  ⟨ParserActions.parsed_lexes actions a.parsed.parsed,
    ParserActions.parsed_in_ebnf a.parsed.parsed⟩

theorem Prepared.equation_correct (a : Prepared source)
    (values derivatives : String → Value ℝ stateShape) (matrices : String → Jacobian stateShape) :
    a.parsed.parsed.ast.Equation (fun name i => (values name)[i])
      (fun name i => (derivatives name)[i]) matrices ↔
      a.kernel.Equation (values a.parsed.parsed.ast.header.state)
        (values a.parsed.parsed.ast.header.input) (derivatives a.parsed.parsed.ast.header.state)
        (a.parsed.parsed.ast.jacobianValue matrices) := by
  rw [a.kernel_lowered]
  exact lowering_chain_correct _ a.resolved values derivatives matrices

theorem Prepared.initialization_correct (a : Prepared source) (values : String → Value ℝ stateShape) :
    a.parsed.parsed.ast.Initial (fun name i => (values name)[i]) ↔
      a.kernel.Initial (values a.parsed.parsed.ast.header.state) := by
  rw [a.kernel_lowered]
  exact initialization_chain_correct _ a.resolved values

/-- Every successful source preparation binds the parsed tokens to that
source and preserves both equations and initialization in its stored kernel.
The matrix is arbitrary: the theorem characterizes the entire solution set. -/
theorem prepare_correct (_checked : prepare source = .ok a)
    (values derivatives : String → Value ℝ stateShape) (matrices : String → Jacobian stateShape) :
    ArrayProfile.parse source = .ok a.parsed.parsed ∧
      Lexes source.toList a.parsed.parsed.ast.tokens ∧
      EBNF.Accepts Generated.sourceGrammar (a.parsed.parsed.tokens.map Token.symbol) ∧
      (a.parsed.parsed.ast.Equation (fun name i => (values name)[i])
        (fun name i => (derivatives name)[i]) matrices ↔
        a.kernel.Equation (values a.parsed.parsed.ast.header.state)
          (values a.parsed.parsed.ast.header.input) (derivatives a.parsed.parsed.ast.header.state)
          (a.parsed.parsed.ast.jacobianValue matrices)) ∧
      (a.parsed.parsed.ast.Initial (fun name i => (values name)[i]) ↔
        a.kernel.Initial (values a.parsed.parsed.ast.header.state)) := by
  -- The dependent result carries these certificates for any inhabitant;
  -- successful preparation exposes that result without an external premise.
  exact ⟨a.parsed.erases, a.source_correct.1, a.source_correct.2,
    a.equation_correct values derivatives matrices, a.initialization_correct values⟩

end Rumoca.ArrayCompiler
