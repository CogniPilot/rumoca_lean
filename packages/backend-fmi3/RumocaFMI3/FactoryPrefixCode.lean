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

def code (message : String) : List Stmt := [
  .branch (.bin .and (.id "logMessage") (.id "loggingOn")) [logCall message] [],
  .ret (some (.id "NULL"))]

end FactoryRejection

namespace FactoryPrefix

def validation (model : Solve.FMI3Model source) : Stmt :=
  .declare "fmi3Boolean" "validIdentity" (.call (.id Identity.function.signature.name)
    [.id "instanceName", .id "instantiationToken", .str (token model), .str " \t\n\r\u000c\u000b"])

def identityGuard : Stmt := .branch (.not (.id "validIdentity"))
  (FactoryRejection.code "Invalid name or instantiation token") []

def capabilityGuard : Stmt := .branch
  (.bin .or (.id "eventModeUsed") (.bin .ne (.id "nRequiredIntermediateVariables") (.nat 0)))
  (FactoryRejection.code "Events and intermediate updates are unsupported") []

def entry (kind : Kind) (rest : List Stmt) : List Stmt :=
  match kind with
  | .me => rest
  | .cs => capabilityGuard :: rest

def body (model : Solve.FMI3Model source) (kind : Kind) (creation : List Stmt) : List Stmt :=
  entry kind (validation model :: identityGuard :: creation)

end FactoryPrefix
end Rumoca.FMI3
