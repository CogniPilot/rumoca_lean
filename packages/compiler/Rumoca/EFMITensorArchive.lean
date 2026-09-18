import Rumoca.EFMITensorProduction
import RumocaEFMI.Archive

/-! Pure assembly of the frozen tensor eFMU product from a development tensor
artifact. The archive members are the pinned tensor square Algorithm Code, the
certified-kernel tensor Production Code, and the three manifests for a packaging
identity and the artifact's model name; the vendored schemas are embedded by the
shared archive generator. Identity fields are supplied explicitly and checked by
the manifest builder. File publication and its independent certificate are
separate layers. -/
namespace Rumoca
open EFMI

/-- The five in-archive code/manifest members of the tensor square eFMU, reusing
the shared `Archive.Code` roster: the pinned tensor Algorithm Code, the
certified-kernel tensor Production Code, and the Algorithm/Production/container
manifests for the artifact's model name and packaging identity. -/
def TensorArtifact.efmiCode (a : TensorArtifact input) (identity : Manifest.Identity) :
    Archive.Code :=
  let documents := TensorManifest.prepare a.name identity EFMI.tensorUnitSource
  ⟨EFMI.tensorUnitSource, EFMI.TensorProduction.render,
    XML.document documents.algorithm, XML.document documents.production,
    XML.document documents.content⟩

/-- Candidate tensor eFMU bytes through the shared stored-ZIP generator. The
result must be bound to the tensor source/manifest semantics and the complete
ZIP byte grammar before it can be published. -/
def TensorArtifact.efmuArchive (a : TensorArtifact input) (identity : Manifest.Identity) :
    Except String ByteArray :=
  Archive.encode (a.efmiCode identity)

end Rumoca
