import RumocaFMI3.Metadata
import RumocaFMI3.IdentityCode
import RumocaCore.FMI3.Lifecycle

/-! Public factory prototypes and admission statements, independent of instance
storage. The creation continuation consumes an already prepared Solve model.
This module contains emission data only; execution proofs live separately. -/
namespace Rumoca.FMI3
open CTree

def Identity.factoryName : Kind → String
  | .me => "fmi3InstantiateModelExchange"
  | .cs => "fmi3InstantiateCoSimulation"

def FactoryArguments.signature (kind : Kind) : Signature :=
  ⟨"fmi3Instance", Identity.factoryName kind,
    [⟨"fmi3String", "instanceName", false⟩,
     ⟨"fmi3String", "instantiationToken", false⟩,
     ⟨"fmi3String", "resourcePath", false⟩,
     ⟨"fmi3Boolean", "visible", false⟩,
     ⟨"fmi3Boolean", "loggingOn", false⟩] ++
    (match kind with | .me => [] | .cs => [
      ⟨"fmi3Boolean", "eventModeUsed", false⟩,
      ⟨"fmi3Boolean", "earlyReturnAllowed", false⟩,
      ⟨"const fmi3ValueReference", "requiredIntermediateVariables", true⟩,
      ⟨"size_t", "nRequiredIntermediateVariables", false⟩]) ++
    [⟨"fmi3InstanceEnvironment", "instanceEnvironment", false⟩,
     ⟨"fmi3LogMessageCallback", "logMessage", false⟩] ++
    (match kind with | .me => [] | .cs => [⟨"fmi3IntermediateUpdateCallback", "intermediateUpdate", false⟩])⟩

namespace FactoryRejection

def logCall (message : String) : Stmt := .eval (.call (.id "logMessage")
  [.id "instanceEnvironment", .id "fmi3Error", .str "logStatus", .str message])

def codeWith (pointerPresent : Expr → Expr) (message : String) : List Stmt := [
  .branch (.bin .and (pointerPresent (.id "logMessage")) (.id "loggingOn")) [logCall message] [],
  .ret (some (.id "NULL"))]

/-- Legacy logical proof view and actual explicit pointer test. -/
def explicitPresent (pointer : Expr) : Expr := .bin .ne pointer Expr.nullPointer
def logicalCode : String → List Stmt := codeWith id
def code : String → List Stmt := codeWith explicitPresent

end FactoryRejection

namespace FactoryPrefix

def validation (model : Solve.FMI3Model source) (tok : String := token model) : Stmt :=
  .declare "fmi3Boolean" "validIdentity" (.call (.id Identity.function.signature.name)
    [.id "instanceName", .id "instantiationToken", .str tok, .str " \t\n\r\u000c\u000b"])

def identityGuardWith (pointerPresent : Expr → Expr) : Stmt := .branch (.not (.id "validIdentity"))
  (FactoryRejection.codeWith pointerPresent "Invalid name or instantiation token") []

def capabilityGuardWith (pointerPresent : Expr → Expr) : Stmt := .branch
  (.bin .or (.id "eventModeUsed") (.bin .ne (.id "nRequiredIntermediateVariables") (.nat 0)))
  (FactoryRejection.codeWith pointerPresent "Events and intermediate updates are unsupported") []

def entryWith (pointerPresent : Expr → Expr) (kind : Kind) (rest : List Stmt) : List Stmt :=
  match kind with
  | .me => rest
  | .cs => capabilityGuardWith pointerPresent :: rest

def bodyWith (pointerPresent : Expr → Expr) (model : Solve.FMI3Model source) (kind : Kind) (creation : List Stmt) (tok : String := token model) : List Stmt :=
  entryWith pointerPresent kind (validation model tok :: identityGuardWith pointerPresent :: creation)

def logicalIdentityGuard : Stmt := identityGuardWith id
def logicalCapabilityGuard : Stmt := capabilityGuardWith id
def logicalEntry := entryWith id
def logicalBody (model : Solve.FMI3Model source) (kind : Kind) (creation : List Stmt)
    (tok : String := token model) : List Stmt := bodyWith id model kind creation tok
def identityGuard : Stmt := identityGuardWith FactoryRejection.explicitPresent
def capabilityGuard : Stmt := capabilityGuardWith FactoryRejection.explicitPresent
def entry := entryWith FactoryRejection.explicitPresent
def body (model : Solve.FMI3Model source) (kind : Kind) (creation : List Stmt)
    (tok : String := token model) : List Stmt :=
  bodyWith FactoryRejection.explicitPresent model kind creation tok

end FactoryPrefix
end Rumoca.FMI3
