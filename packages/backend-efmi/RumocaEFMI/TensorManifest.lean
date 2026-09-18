import RumocaEFMI.Manifest
import RumocaEFMI.TensorProductionCode

/-! Algorithm Code and Production Code manifests for the fixed-extent tensor
square profile. The trees describe the same logical variables the tensor
Algorithm Code declares and the tensor Production Code exposes, as eFMI array
variables with dimensions per the vendored ProductionCode/AlgorithmCode variable
schemas. The emitter consumes the complete code strings; it performs no DAE
lowering and selects no solver. UUIDs and the UTC generation time come from the
packaging identity. Schema membership and archive graph obligations are separate
layers, established at the checker boundary. -/
namespace Rumoca.EFMI.TensorManifest
open XML
open Rumoca.EFMI.Manifest (node baseAttributes files file algorithmFileId productionFileId originId
  Identity)

/-! ### Logical variables and methods of the tensor square profile

The array variables `u` (input), `x` (output square) and `J` (output Jacobian)
carry their fixed extents as dimensions; `samplePeriod` is the scalar clock
constant the block declares. -/

structure Var where
  algId : String
  compId : String
  name : String
  causality : String
  start : String
  dims : List Nat
  deriving Repr

def inputVar : Var := ⟨"AV_Input", "C_Input", "u", "input", "0", [2]⟩
def squareVar : Var := ⟨"AV_State", "C_State", "x", "output", "0", [2]⟩
def jacobianVar : Var := ⟨"AV_Jacobian", "C_Jacobian", "J", "output", "0", [2, 2]⟩
def clockVar : Var := ⟨"AV_Clock", "C_Clock", "samplePeriod", "constant", "1", []⟩

/-- Every logical variable of the profile, in declaration order. -/
def logicalVars : List Var := [inputVar, squareVar, jacobianVar, clockVar]

/-- The array variables that map to C struct members of `Model`. The scalar
clock constant is an Algorithm-level constant and is not a mapped C component. -/
def mappedVariables : List Var := [inputVar, squareVar, jacobianVar]

structure Method where
  af : String
  cf : String
  cp : String
  cr : String
  name : String
  fn : String
  deriving Repr

def startup : Method := ⟨"AF_Startup", "CF_Startup", "CP_Startup_self", "CR_Startup", "Startup",
  TensorProduction.startupName⟩
def recalibrate : Method := ⟨"AF_Recalibrate", "CF_Recalibrate", "CP_Recalibrate_self", "CR_Recalibrate",
  "Recalibrate", TensorProduction.recalibrateName⟩
def doStep : Method := ⟨"AF_DoStep", "CF_DoStep", "CP_DoStep_self", "CR_DoStep", "DoStep",
  TensorProduction.doStepName⟩

def methods : List Method := [startup, recalibrate, doStep]

def errorSignalId : String := "ERROR_Status"
def statusComponentId : String := "C_ErrorStatus"
def realTypeId : String := "TD_EfmiReal"
def statusTypeId : String := "TD_EfmiStatus"
def realTargetId : String := "TT_EfmiReal"
def statusTargetId : String := "TT_EfmiStatus"
def modelTypeId : String := "TD_Model"

/-! ### Dimensions

Each fixed extent becomes a `Dimension` element with a one-based `number` and its
constant `size`, per the vendored dimension schemas. A scalar variable has no
`Dimensions` element. -/

def dimensionNodes (dims : List Nat) : List Element :=
  if dims.isEmpty then []
  else [node "Dimensions" []
    (dims.mapIdx (fun i size => node "Dimension" [("number", toString (i + 1)), ("size", toString size)]))]

/-! ### Algorithm Code manifest -/

def algorithmVariable (v : Var) : Element :=
  { name := "RealVariable",
    attributes := [("id", v.algId), ("name", v.name), ("blockCausality", v.causality),
      ("start", v.start)],
    children := dimensionNodes v.dims }

def blockMethod (m : Method) : Element :=
  node "BlockMethod" [("id", m.af), ("kind", m.name)]

def algorithm (modelName : String) (identity : Identity) (source : String) : Element :=
  node "Manifest"
    ([("xsdVersion", "0.14.0"), ("kind", "AlgorithmCode"), ("fileRefId", algorithmFileId)] ++
      baseAttributes modelName identity identity.algorithm)
    [files algorithmFileId "model.alg" source.toUTF8,
      node "Clock" [("id", "CLOCK_Period"), ("variableRefId", clockVar.algId)],
      node "BlockMethods" [] (methods.map blockMethod),
      node "ErrorSignalStatus" [("id", errorSignalId)],
      node "Units", node "Variables" [] (logicalVars.map algorithmVariable)]

/-! ### Production Code manifest -/

def targetType (id kind coded : String) : Element :=
  node "TargetType" [("id", id), ("kind", kind), ("codedType", coded)]

def aliasType (id name target : String) : Element :=
  node "Typedef" [("id", id), ("name", name)] [node "Alias" [("targetTypeRefId", target)]]

def component (id name typeId : String) (dims : List Nat) : Element :=
  { name := "Component",
    attributes := [("id", id), ("name", name), ("typeDefRefId", typeId)],
    children := dimensionNodes dims }

def modelType : Element :=
  node "Typedef" [("id", modelTypeId), ("name", "Model")]
    [node "Components" []
      (mappedVariables.map (fun v => component v.compId v.name realTypeId v.dims) ++
        [component "C_Clock" clockVar.name realTypeId [],
         component statusComponentId TensorProduction.statusName statusTypeId []])]

def function (m : Method) : Element :=
  node "Function" [("id", m.cf), ("name", m.fn)]
    [node "ReturnParameter" [("id", m.cr), ("typeDefRefId", statusTypeId)],
      node "FormalParameters" []
        [node "FormalParameter" [("id", m.cp), ("name", "self"), ("number", "0"),
          ("typeDefRefId", modelTypeId), ("pointer", "true")]]]

def dataReference (m : Method) (foreignId component : String) : Element :=
  node "DataReference" []
    [node "ForeignVariableReference" [("manifestReferenceRefId", originId), ("foreignRefId", foreignId)],
      node "FormalParameter" [("formalParameterRefId", m.cp), ("componentIdentifier", component)]]

def dataMapping (m : Method) (v : Var) : Element := dataReference m v.algId v.name

def statusMapping (m : Method) : Element := dataReference m errorSignalId TensorProduction.statusName

def functionMapping (m : Method) : Element :=
  node "FunctionReference" []
    [node "ForeignFunctionReference" [("manifestReferenceRefId", originId), ("foreignRefId", m.af)],
      node "GlobalFunction" [("functionRefId", m.cf)]]

def codeFile : Element :=
  node "CodeFile" [("id", "CODE_Production"), ("fileType", "ProductionCode"), ("codeType", "SourceFile")]
    [node "FileReference" [("fileRefId", productionFileId)],
      node "Typedefs" []
        [aliasType realTypeId "EfmiReal" realTargetId,
         aliasType statusTypeId "EfmiStatus" statusTargetId, modelType],
      node "Functions" [] (methods.map function)]

def logicalData : Element :=
  node "LogicalData" []
    [node "DataReferences" []
      ((methods.flatMap fun m => mappedVariables.map (dataMapping m)) ++ methods.map statusMapping),
      node "FunctionReferences" [] (methods.map functionMapping)]

def production (modelName : String) (identity : Identity) (algorithmXML : String) : Element :=
  node "Manifest"
    ([("xsdVersion", "0.17.0"), ("kind", "ProductionCode")] ++
      baseAttributes modelName identity identity.production)
    [node "ManifestReferences" [] [node "ManifestReference" [("id", originId),
      ("manifestRefId", identity.algorithm), ("checksum", SHA1.hash algorithmXML.toUTF8),
      ("origin", "true")]],
      files productionFileId "production.c" TensorProduction.render.toUTF8,
      node "CodeContainer" [("language", "C"), ("standard", "C11"), ("platform", "Legacy"),
        ("floatPrecision", "64-bit")]
        [{ name := "Target", text := "Generic" },
          node "TargetTypes" []
            [targetType realTargetId "efmiFloat64" "double",
             targetType statusTargetId "efmiInteger32" "int32_t"],
          node "CodeFiles" [] [codeFile], logicalData]]

/-! ### The manifest documents

The two representation manifests, hashed into the container content the same way
the scalar profile does. -/

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

/-- Hash each already serialized dependency before constructing its dependents,
with no XML reformatting between the steps. -/
def prepare (modelName : String) (identity : Identity) (algorithmSource : String) : Documents :=
  let a := algorithm modelName identity algorithmSource
  let p := production modelName identity (document a)
  ⟨a, p, content modelName identity (document a) (document p)⟩

end Rumoca.EFMI.TensorManifest
