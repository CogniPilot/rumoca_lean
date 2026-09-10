import RumocaEFMI.ProductionCode

/-! Typed names and references for the tiny Algorithm/Production manifests.
These describe the prepared products; they do not lower equations or select a
solver. XML serialization and the complete archive graph are separate layers.
Tensor shape is retained on logical variables, including rank-zero variables. -/
namespace Rumoca.EFMI.Metadata

inductive Variable where
  | state | clock
  deriving Repr, BEq, DecidableEq

def variables : List Variable := [.state, .clock]
def methods : List GALEC.Method := [.startup, .recalibrate, .doStep]

def Variable.name : Variable → String
  | .state => "x"
  | .clock => "samplePeriod"

def Variable.id : Variable → String
  | .state => "AV_State"
  | .clock => "AV_Clock"

def Variable.componentId : Variable → String
  | .state => "C_State"
  | .clock => "C_Clock"

def Variable.shape (_ : Variable) : Tensor.Shape := Tensor.scalar
def Variable.scalar (_ : Variable) : CHeader.Scalar := .real64

def algorithmMethodName : GALEC.Method → String
  | .startup => "Startup"
  | .recalibrate => "Recalibrate"
  | .doStep => "DoStep"

def algorithmMethodId (method : GALEC.Method) : String := "AF_" ++ algorithmMethodName method
def functionId (method : GALEC.Method) : String := "CF_" ++ algorithmMethodName method
def parameterId (method : GALEC.Method) : String := "CP_" ++ algorithmMethodName method ++ "_self"
def returnId (method : GALEC.Method) : String := "CR_" ++ algorithmMethodName method

def targetKind : CHeader.Scalar → String
  | .real64 => "efmiFloat64"
  | .status32 => "efmiInteger32"

def targetTypeId (scalar : CHeader.Scalar) : String := "TT_" ++ scalar.alias
def scalarTypeId (scalar : CHeader.Scalar) : String := "TD_" ++ scalar.alias
def modelTypeId : String := "TD_Model"
def errorSignalId : String := "ERROR_Status"
def statusComponentId : String := "C_ErrorStatus"

structure FunctionDescription where
  id : String
  name : String
  returnId : String
  returnTypeId : String
  parameterId : String
  parameterName : String
  parameterTypeId : String
  pointer : Bool
  deriving Repr, BEq, DecidableEq

def functionDescription (module : Production.Module) (method : GALEC.Method) : FunctionDescription :=
  ⟨functionId method, (module.method method).signature.name, returnId method,
    scalarTypeId .status32, parameterId method, "self", modelTypeId, true⟩

/-- A reference through an instance formal parameter, as required by eFMI
§5.1.5. Each method's formal parameter has its own manifest identifier. -/
structure DataReference where
  foreignVariableId : String
  formalParameterId : String
  componentIdentifier : String
  deriving Repr, BEq, DecidableEq

def dataReference (method : GALEC.Method) (var : Variable) : DataReference :=
  ⟨var.id, parameterId method, var.name⟩

/-- The standard's error anchor is an interface observation, not a GALEC
model variable. Each method exposes it through its actual instance formal. -/
def statusReference (method : GALEC.Method) : DataReference :=
  ⟨errorSignalId, parameterId method, CHeader.statusName⟩

def referenceExpression (module : Production.Module) (method : GALEC.Method)
    (var : Variable) : CTree.Expr :=
  .field (.id (functionDescription module method).parameterName)
    (dataReference method var).componentIdentifier true

end Rumoca.EFMI.Metadata
