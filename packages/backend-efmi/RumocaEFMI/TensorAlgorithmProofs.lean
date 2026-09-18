import RumocaEFMI.TensorAlgorithmCode
import GALECParser.Parser

/-! Actual source grammar processing of the tensor Algorithm Code, checked in
Lean independently of the native table producer. The emitted text lexes and
parses to the resolved tensor square block, which denotes the prepared square
kernel. The refinement of that kernel is in `TensorAlgorithmCode`. -/
open _root_.Parser

namespace Rumoca.EFMI
open Rumoca.Tensor Rumoca.Solve

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem tensor_lexical :
    Scanner.lex GALEC.Syntax.tensorScanner tensorUnitSource = .ok GALEC.Syntax.tensorUnit.tokens := by
  rfl

theorem tensor_parsed : ∃ parsed, GALEC.Syntax.parseTensor tensorUnitSource = .ok parsed ∧
    parsed.ast = GALEC.Syntax.tensorUnit :=
  GALEC.Syntax.parseTensor_complete _ _
    ((Scanner.lex_correct _ _ _).mp tensor_lexical) GALEC.Syntax.tensorUnit_resolved

theorem tensor_render_parses (m : TensorModel shape) :
    ∃ parsed, GALEC.Syntax.parseTensor (renderTensorAlgorithm m) = .ok parsed ∧
      parsed.ast = GALEC.Syntax.tensorUnit := by
  rw [tensor_emission_is_unit]
  exact tensor_parsed

/-- Name-checked tensor source denotes the admitted square profile and its
prepared pointwise kernel, not only its token shape. -/
def TensorDenotes (parsed : GALEC.Syntax.TensorBlock) (kernel : PointwiseIVP shape) : Prop :=
  GALEC.Syntax.ResolvedTensor parsed ∧ kernel = squareKernel shape

theorem tensor_render_denotes (m : TensorModel shape) :
    ∃ parsed, GALEC.Syntax.parseTensor (renderTensorAlgorithm m) = .ok parsed ∧
      TensorDenotes parsed.ast m.kernel := by
  obtain ⟨p, hp, hast⟩ := tensor_render_parses m
  exact ⟨p, hp, hast ▸ p.resolved, m.profile⟩

end Rumoca.EFMI
