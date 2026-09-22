import Rumoca.TensorArtifact
import RumocaEFMI.TensorAlgorithmProofs

/-! Development tensor Algorithm Code product. The array/tensor profile is not
admitted to eFMI CLI output; this package product renders the eFMI Algorithm
Code for the prepared pointwise square kernel and carries its correctness
theorem. The default CLI keeps rejecting tensor eFMI output. -/
namespace Rumoca
open Rumoca.EFMI Rumoca.Tensor Rumoca.Solve

/-- The prepared kernel of the pinned `TensorSquare` array AST is exactly the
tensor square kernel the eFMI Algorithm Code renders. The array frontend and
the eFMI backend therefore agree on the pointwise problem, without either side
reconstructing it. -/
theorem square_prepared_kernel :
    ArrayProfile.Solved.lower (ArrayProfile.DAE.lower
        (ArrayProfile.Flat.lower squareAst squareAst_resolved))
      = EFMI.squareKernel ArrayProfile.stateShape := by
  have hlow : ArrayProfile.Solved.lower? (ArrayProfile.DAE.lower
      (ArrayProfile.Flat.lower squareAst squareAst_resolved))
      = some (EFMI.squareKernel ArrayProfile.stateShape) := rfl
  exact Option.some.inj
    ((ArrayProfile.Solved.lower_checked _).symm.trans hlow)

/-- Development tensor Algorithm Code artifact from a prepared array source
whose kernel is the tensor square kernel. -/
structure TensorAlgorithmArtifact (source : String) where
  prepared : ArrayCompiler.Prepared source
  square : prepared.kernel = EFMI.squareKernel ArrayProfile.stateShape

def TensorAlgorithmArtifact.model (a : TensorAlgorithmArtifact source) :
    EFMI.TensorModel ArrayProfile.stateShape := ⟨a.prepared.kernel, a.square⟩

def TensorAlgorithmArtifact.algorithmSource (a : TensorAlgorithmArtifact source) : String :=
  EFMI.renderTensorAlgorithm a.model

/-- Compiler correctness: the emitted tensor Algorithm Code parses to the
resolved tensor square block that denotes the artifact's prepared kernel. -/
theorem TensorAlgorithmArtifact.algorithm_correct (a : TensorAlgorithmArtifact source) :
    ∃ parsed, GALEC.Syntax.parseTensor a.algorithmSource = .ok parsed ∧
      EFMI.TensorDenotes parsed.ast a.prepared.kernel :=
  EFMI.tensor_render_denotes a.model

/-- The pinned `TensorSquare` fixture yields a tensor Algorithm Code artifact,
so the correctness theorem applies to the actual development source case. -/
def squareAlgorithmArtifact (a : TensorArtifact input)
    (hast : a.prepared.parsed.parsed.ast = squareAst) :
    TensorAlgorithmArtifact input.source where
  prepared := a.prepared
  square :=
    (congrArg Solve.TensorFMI3Model.ivp (TensorArtifact.tensorModel_square a hast)).trans
      square_prepared_kernel

end Rumoca
