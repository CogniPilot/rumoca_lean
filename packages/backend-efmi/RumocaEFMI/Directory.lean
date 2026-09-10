import RumocaEFMI.Manifest

/-! File adapter for the frozen two-representation directory profile. Reading
identity fields only proposes data: the actual-file checker must still bind
every complete manifest to its independently read code members. This is not
a general XML parser or an archive conformance checker. -/
namespace Rumoca.EFMI.Directory
open System

def algorithmDirectory : FilePath := "AlgorithmCode"
def productionDirectory : FilePath := "ProductionCode"
def manifestName : FilePath := "manifest.xml"
def contentName : FilePath := "__content.xml"
def algorithmName : FilePath := "model.alg"
def productionName : FilePath := "production.c"

structure Snapshot where
  algorithm : String
  production : String
  algorithmXML : String
  productionXML : String
  contentXML : String
  identity : Manifest.Identity

/-- Extract one candidate attribute from our emitted root start tag. The full
serialization equality checked later rejects duplicate attributes, additional
markup and mismatched identities. Escaped identity fields are outside this
directory adapter's UUID/date profile. -/
private def rootAttribute (xml tag key : String) : Except String String := do
  let _declaration :: header :: _ := xml.splitOn "\n"
    | throw s!"missing {tag} root header"
  unless header.startsWith ("<" ++ tag ++ " ") do throw s!"expected {tag} root header"
  let [_, rest] := header.splitOn (" " ++ key ++ "=\"")
    | throw s!"missing or repeated {tag}.{key}"
  let value :: _ :: _ := rest.splitOn "\""
    | throw s!"unterminated {tag}.{key}"
  if value.isEmpty || value.contains '&' || value.contains '<' then
    throw s!"unsupported {tag}.{key}"
  return value

/-- Propose the same identity fields from directory or archive member strings.
No file is reread while constructing the later code/manifest certificate. -/
def snapshot (algorithm production algorithmXML productionXML contentXML : String) : Except String Snapshot := do
  let identity := Manifest.Identity.mk
    (← rootAttribute contentXML "Content" "id")
    (← rootAttribute algorithmXML "Manifest" "id")
    (← rootAttribute productionXML "Manifest" "id")
    (← rootAttribute contentXML "Content" "generationDateAndTime")
  return { algorithm, production, algorithmXML, productionXML, contentXML, identity }

def read (root : FilePath) : IO Snapshot := do
  let candidate := snapshot
    (← IO.FS.readFile (root / algorithmDirectory / algorithmName))
    (← IO.FS.readFile (root / productionDirectory / productionName))
    (← IO.FS.readFile (root / algorithmDirectory / manifestName))
    (← IO.FS.readFile (root / productionDirectory / manifestName))
    (← IO.FS.readFile (root / contentName))
  match candidate with
    | .ok value => pure value
    | .error error => throw (IO.userError error)

end Rumoca.EFMI.Directory
