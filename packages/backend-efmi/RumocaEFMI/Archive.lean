import RumocaEFMI.Directory
import RumocaEFMI.StoredZIP
import RumocaEFMIResources

/-! Exact members of the tiny two-representation eFMU. This layer assembles
prepared code and manifest strings; it performs no compiler lowering. The
schemas are embedded from the pinned release, independently of any archive
candidate. Publication requires the compiler's composed archive certificate. -/
namespace Rumoca.EFMI.Archive
open StoredZIP

inductive Member where
  | content | algorithmManifest | algorithm | productionManifest | production
  deriving DecidableEq, Repr

def Member.name : Member → String
  | .content => Directory.contentName.toString
  | .algorithmManifest => Directory.algorithmDirectory.toString ++ "/" ++ Directory.manifestName.toString
  | .algorithm => Directory.algorithmDirectory.toString ++ "/" ++ Directory.algorithmName.toString
  | .productionManifest => Directory.productionDirectory.toString ++ "/" ++ Directory.manifestName.toString
  | .production => Directory.productionDirectory.toString ++ "/" ++ Directory.productionName.toString

def members : List Member := [.content, .algorithmManifest, .algorithm, .productionManifest, .production]

structure Code where
  algorithm : String
  production : String
  algorithmXML : String
  productionXML : String
  contentXML : String

def Code.text (code : Code) : Member → String
  | .content => code.contentXML
  | .algorithmManifest => code.algorithmXML
  | .algorithm => code.algorithm
  | .productionManifest => code.productionXML
  | .production => code.production

def Code.entries (code : Code) : List Entry :=
  members.map fun member => ⟨member.name, (code.text member).toUTF8⟩

def schemaEntries : List Entry :=
  Resources.schemas.map fun resource => ⟨resource.name, resource.text.toUTF8⟩

def entries (code : Code) : List Entry := code.entries ++ schemaEntries

def paths : List String := members.map Member.name ++ Resources.schemas.map Resources.Resource.name

def lookup (entries : List Entry) (name : String) : Option ByteArray :=
  (entries.find? fun entry => entry.name == name).map Entry.bytes

/-- Candidate generation. Its result must be bound to source/manifest
semantics and the complete ZIP byte grammar before it can be published. -/
def encode (code : Code) : Except String ByteArray := StoredZIP.encode (entries code)

end Rumoca.EFMI.Archive
