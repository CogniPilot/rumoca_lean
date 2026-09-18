import Rumoca.EFMITensorAlgorithm
import RumocaEFMI.TensorProductionProofs
import RumocaEFMI.TensorManifestProofs

/-! Development tensor Production Code and manifest product. The array/tensor
profile is not admitted to eFMI CLI output; this package product renders the
eFMI Production Code and the Algorithm/Production/container manifests for the
prepared pointwise square kernel and carries their correctness theorems. The
default CLI keeps rejecting tensor eFMI output. -/
namespace Rumoca
open Rumoca.EFMI Rumoca.EFMI.TensorProduction Rumoca.EFMI.TensorManifest XML

/-- Development tensor Production Code and manifest artifact, built on the tensor
Algorithm Code artifact. It renders the certified-kernel Production translation
unit and the manifest documents for a packaging identity and model name. -/
structure TensorProductionArtifact (source : String) where
  algorithm : TensorAlgorithmArtifact source

/-- The emitted Production Code translation unit. -/
def TensorProductionArtifact.productionSource (_a : TensorProductionArtifact source) : String :=
  TensorProduction.render

/-- The emitted Algorithm Code text, from the tensor Algorithm Code product. -/
def TensorProductionArtifact.algorithmSource (a : TensorProductionArtifact source) : String :=
  a.algorithm.algorithmSource

/-- The Algorithm/Production/container manifest documents for a packaging
identity and model name. -/
def TensorProductionArtifact.documents (a : TensorProductionArtifact source)
    (modelName : String) (identity : Manifest.Identity) : TensorManifest.Documents :=
  TensorManifest.prepare modelName identity a.algorithmSource

/-- Compiler correctness for the Production Code member: the emitted translation
unit satisfies its contract, so the derivative method computes the prepared
derivative, the Jacobian output computes the doubled input, and the certified
tensor C artifact contract holds, universal in the state shape. -/
theorem TensorProductionArtifact.production_correct (a : TensorProductionArtifact source) :
    TensorProduction.Contract a.productionSource :=
  TensorProduction.production_correct _ rfl

/-- Compiler correctness for the manifest members: when the documents lie in the
checked XML output profile, each serializes to bytes the output grammar relates
back to its tree, and the production origin reference and the container
representations hash exactly those serialized dependency bytes. -/
theorem TensorProductionArtifact.manifests_correct (a : TensorProductionArtifact source)
    (modelName : String) (identity : Manifest.Identity)
    (valid : (a.documents modelName identity).valid = true) :
    Document (a.documents modelName identity).algorithm
        (document (a.documents modelName identity).algorithm) ∧
    Document (a.documents modelName identity).production
        (document (a.documents modelName identity).production) ∧
    Document (a.documents modelName identity).content
        (document (a.documents modelName identity).content) ∧
    (∃ origin, Manifest.select (a.documents modelName identity).production
        ["ManifestReferences", "ManifestReference"] = [origin] ∧
      origin.attributes.lookup "checksum" =
        some (SHA1.hash (document (a.documents modelName identity).algorithm).toUTF8)) := by
  refine ⟨(documents_valid _ valid).1, (documents_valid _ valid).2.1,
    (documents_valid _ valid).2.2, ?_⟩
  exact (prepare_checksums modelName identity a.algorithmSource).1

/-- The pinned `TensorSquare` fixture yields a tensor Production artifact, so the
correctness theorems apply to the actual development source case. -/
def squareProductionArtifact (a : TensorArtifact input)
    (hast : a.prepared.parsed.parsed.ast = squareAst) :
    TensorProductionArtifact input.source where
  algorithm := squareAlgorithmArtifact a hast

end Rumoca
