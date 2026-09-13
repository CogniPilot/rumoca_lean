import RumocaCore.FMI3.Lifecycle
import RumocaC.InitializationCode

/-! Complete inline instance initialization for permanent typed storage.
The model initial value and its provenance come from prepared Solve IR.
All adapter-owned clock/policy fields are explicitly reset on reuse. -/
namespace Rumoca.FMI3.InstanceInitialization
open CTree

def field (name : String) : Expr := .field (.id "m") name true
def state : Expr := .field (field "model") "x"
def put (name : String) (value : Expr) : Stmt := .assign (field name) value

def code (model : Solve.Model source) (kind : Kind) : List Stmt := [
  (CInitialization.emit model state).statement,
  put "time" (.nat 0), put "timeMin" (.nat 0), put "eventTime" (.nat 0),
  put "lastCompleted" (.nat 0), put "stop" (.nat 0), put "stopDefined" (.nat 0),
  put "mode" (.nat Mode.instantiated.code), put "kind" (.nat (match kind with | .me => 0 | .cs => 1)),
  put "environment" (.id "instanceEnvironment"), put "logger" (.id "logMessage"),
  put "logging" (.id "loggingOn")]

def returnHandle : Stmt := .ret (some (.cast "fmi3Instance" (.id "m")))

end Rumoca.FMI3.InstanceInitialization
