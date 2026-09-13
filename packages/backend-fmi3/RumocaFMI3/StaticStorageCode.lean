import RumocaC.ObjectDeclarationCode

/-! Permanent FMI adapter storage, expressed with the shared C declarations.
The Model member is the prepared Solve kernel's scalar state; the remaining
fields are FMI lifecycle/host/slot bookkeeping. No lowering or source-name
resolution belongs here. Runtime.render emits this structured product. -/
namespace Rumoca.FMI3.StaticStorage
open CObject

/-- Generation-time capacity of the current embedded FMI profile. Both ME and
CS share these permanently existing objects; exhaustion is an FMI error path.
The proofs below the deployment boundary remain generic in the capacity. -/
def deploymentCapacity : Nat := 32

def modelRecord : Record := ⟨"Model", [⟨"double", "x"⟩]⟩

def instanceRecord : Record := ⟨"Instance", [
  ⟨"Model", "model"⟩,
  ⟨"double", "time"⟩, ⟨"double", "stop"⟩, ⟨"double", "timeMin"⟩,
  ⟨"double", "eventTime"⟩, ⟨"double", "lastCompleted"⟩,
  ⟨"int", "kind"⟩, ⟨"int", "mode"⟩,
  ⟨"fmi3Boolean", "stopDefined"⟩, ⟨"fmi3Boolean", "logging"⟩,
  ⟨"fmi3InstanceEnvironment", "environment"⟩,
  ⟨"fmi3LogMessageCallback", "logger"⟩, ⟨"size_t", "slot"⟩]⟩

def instances (capacity : Nat) : StaticArray := ⟨"Instance", "rumoca_instances", capacity⟩
def flags (capacity : Nat) : StaticArray := ⟨"atomic_bool", "rumoca_instance_flags", capacity⟩
def count (capacity : Nat) : Constant := ⟨"size_t", "rumoca_instance_capacity", capacity⟩

def render (capacity : Nat) : String :=
  modelRecord.render ++ instanceRecord.render ++
    (instances capacity).render ++ (flags capacity).render ++ (count capacity).render

end Rumoca.FMI3.StaticStorage
