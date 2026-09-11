import Rumoca.EFMI
import RumocaEFMI.Archive

/-! Pure preparation of the frozen eFMU product from an existing compiler
artifact. Identity fields are supplied explicitly and checked by the manifest
builder. File publication and its independent certificate are separate. -/
namespace Rumoca

def Artifact.archiveCode (a : Artifact source) (identity : EFMI.Manifest.Identity) :
    Except String EFMI.Archive.Code := do
  let emission ← EFMI.Production.StartupMap.emit a.algorithmSolve
  let documents ← EFMI.Manifest.checked a.parsed.ast.name identity a.algorithmSource emission.module
  return ⟨a.algorithmSource, emission.document.render, XML.document documents.val.algorithm,
    XML.document documents.val.production, XML.document documents.val.content⟩

def Artifact.efmuArchive (a : Artifact source) (identity : EFMI.Manifest.Identity) :
    Except String ByteArray := do
  EFMI.Archive.encode (← a.archiveCode identity)

end Rumoca
