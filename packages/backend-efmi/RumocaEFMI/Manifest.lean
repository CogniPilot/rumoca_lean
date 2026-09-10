import RumocaEFMI.Metadata
import RumocaEFMI.Identity
import SHA1.Basic
import XML.Syntax

/-! Manifest construction for the prepared tiny Algorithm/Production products.
The emitter consumes metadata and complete code strings; it performs no DAE
lowering or solver selection. UUIDs and the UTC generation time are supplied
by the packaging layer. Schema, graph and actual-byte obligations are separate
from constructing these trees. -/
namespace Rumoca.EFMI.Manifest
open Metadata
open XML

def node (name : String) (attrs : List (String × String) := [])
    (children : List Element := []) : Element :=
  { name, attributes := attrs, children }

def algorithmFileId : String := "FILE_Algorithm"
def productionFileId : String := "FILE_Production"
def originId : String := "ORIGIN_Algorithm"

def baseAttributes (modelName : String) (identity : Identity) (id : String) : List (String × String) :=
  [("efmiVersion", "1.0.0"), ("id", id), ("name", modelName),
    ("generationDateAndTime", identity.generated), ("generationTool", "lean_rumoca")]

def file (id name : String) (bytes : ByteArray) : Element :=
  node "File" [("id", id), ("name", name), ("path", "./"),
    ("needsChecksum", "true"), ("checksum", SHA1.hash bytes), ("role", "Code")]

def files (id name : String) (bytes : ByteArray) : Element :=
  node "Files" [] [
    node "File" [("id", "FILE_Manifest"), ("name", "manifest.xml"), ("path", "./"),
      ("needsChecksum", "false"), ("role", "Manifest")], file id name bytes]

def algorithmVariable (var : Variable) : Element :=
  node "RealVariable" [("id", var.id), ("name", var.name),
    ("blockCausality", match var with | .state => "output" | .clock => "constant"),
    ("start", match var with | .state => "0" | .clock => "1")]

def blockMethod (method : GALEC.Method) : Element :=
  node "BlockMethod" [("id", algorithmMethodId method), ("kind", algorithmMethodName method)]

def algorithm (modelName : String) (identity : Identity) (source : String) : Element :=
  node "Manifest"
    ([("xsdVersion", "0.14.0"), ("kind", "AlgorithmCode"), ("fileRefId", algorithmFileId)] ++
      baseAttributes modelName identity identity.algorithm)
    [files algorithmFileId "model.alg" source.toUTF8,
      node "Clock" [("id", "CLOCK_Period"), ("variableRefId", Variable.clock.id)],
      node "BlockMethods" [] (methods.map blockMethod),
      node "ErrorSignalStatus" [("id", "ERROR_Status")],
      node "Units", node "Variables" [] (variables.map algorithmVariable)]

def targetType (scalar : CHeader.Scalar) : Element :=
  node "TargetType" [("id", targetTypeId scalar), ("kind", targetKind scalar),
    ("codedType", scalar.spelling)]

def scalarType (scalar : CHeader.Scalar) : Element :=
  node "Typedef" [("id", scalarTypeId scalar), ("name", scalar.alias)]
    [node "Alias" [("targetTypeRefId", targetTypeId scalar)]]

def component (var : Variable) : Element :=
  node "Component" [("id", var.componentId), ("name", var.name),
    ("typeDefRefId", scalarTypeId var.scalar)]

def modelType : Element :=
  node "Typedef" [("id", modelTypeId), ("name", "Model")]
    [node "Components" [] (variables.map component)]

def formalParameter (description : FunctionDescription) : Element :=
  node "FormalParameter" [("id", description.parameterId), ("name", description.parameterName),
    ("number", "0"), ("typeDefRefId", description.parameterTypeId),
    ("pointer", if description.pointer then "true" else "false")]

def function (module : Production.Module) (method : GALEC.Method) : Element :=
  let description := functionDescription module method
  node "Function" [("id", description.id), ("name", description.name)]
    [node "ReturnParameter" [("id", description.returnId), ("typeDefRefId", description.returnTypeId)],
      node "FormalParameters" [] [formalParameter description]]

def dataMapping (method : GALEC.Method) (var : Variable) : Element :=
  let reference := dataReference method var
  node "DataReference" [] [
    node "ForeignVariableReference" [("manifestReferenceRefId", originId),
      ("foreignRefId", reference.foreignVariableId)],
    node "FormalParameter" [("formalParameterRefId", reference.formalParameterId),
      ("componentIdentifier", reference.componentIdentifier)]]

def functionMapping (method : GALEC.Method) : Element :=
  node "FunctionReference" [] [
    node "ForeignFunctionReference" [("manifestReferenceRefId", originId),
      ("foreignRefId", algorithmMethodId method)],
    node "GlobalFunction" [("functionRefId", functionId method)]]

def codeFile (module : Production.Module) : Element :=
  node "CodeFile" [("id", "CODE_Production"), ("fileType", "ProductionCode"),
    ("codeType", "SourceFile")]
    [node "FileReference" [("fileRefId", productionFileId)],
      node "Typedefs" [] ([CHeader.Scalar.real64, .status32].map scalarType ++ [modelType]),
      node "Functions" [] (methods.map (function module))]

def logicalData : Element := node "LogicalData" [] [
  node "DataReferences" [] (methods.flatMap fun method => variables.map (dataMapping method)),
  node "FunctionReferences" [] (methods.map functionMapping)]

def production (modelName : String) (identity : Identity) (algorithmXML : String)
    (module : Production.Module) : Element :=
  node "Manifest"
    ([("xsdVersion", "0.17.0"), ("kind", "ProductionCode")] ++
      baseAttributes modelName identity identity.production)
    [node "ManifestReferences" [] [node "ManifestReference" [("id", originId),
      ("manifestRefId", identity.algorithm), ("checksum", SHA1.hash algorithmXML.toUTF8),
      ("origin", "true")]],
      files productionFileId "production.c" module.render.toUTF8,
      node "CodeContainer" [("language", "C"), ("standard", "C11"), ("platform", "Legacy"),
        ("floatPrecision", "64-bit")] [
        { name := "Target", text := "Generic" },
        node "TargetTypes" [] ([CHeader.Scalar.real64, .status32].map targetType),
        node "CodeFiles" [] [codeFile module], logicalData]]

def representation (name kind id xml : String) : Element :=
  node "ModelRepresentation" [("name", name), ("kind", kind), ("manifest", "manifest.xml"),
    ("checksum", SHA1.hash xml.toUTF8), ("manifestRefId", id)]

def content (modelName : String) (identity : Identity) (algorithmXML productionXML : String) : Element :=
  node "Content" ([("xsdVersion", "0.11.0")] ++ baseAttributes modelName identity identity.container)
    [representation "AlgorithmCode" "AlgorithmCode" identity.algorithm algorithmXML,
      representation "ProductionCode" "ProductionCode" identity.production productionXML]

structure Documents where
  algorithm : Element
  production : Element
  content : Element
  deriving Repr

def Documents.valid (documents : Documents) : Bool :=
  documents.algorithm.valid && documents.production.valid && documents.content.valid

/-- Hash each already serialized dependency before constructing its dependents.
No XML reformatting or newline normalization is allowed between these steps. -/
def prepare (modelName : String) (identity : Identity) (algorithmSource : String)
    (module : Production.Module) : Documents :=
  let a := algorithm modelName identity algorithmSource
  let p := production modelName identity (document a) module
  ⟨a, p, content modelName identity (document a) (document p)⟩

/-- The candidate construction cannot authorize malformed XML. The retained
proof licenses the independent output grammar for all three documents. -/
def checked (modelName : String) (identity : Identity) (algorithmSource : String) (module : Production.Module) :
    Except String { documents : Documents // documents.valid = true } :=
  if identity.valid then
    let result := prepare modelName identity algorithmSource module
    if h : result.valid = true then .ok ⟨result, h⟩
    else .error "manifest outside the checked XML output profile"
  else .error "invalid eFMI manifest UUIDs or UTC generation timestamp"

end Rumoca.EFMI.Manifest
