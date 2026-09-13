import RumocaFMI3.InstanceSlotCode
import RumocaFMI3.FactoryPrefixCode
import RumocaC.AtomicScanCode

/-! The creation suffix reserves a permanently existing typed array element,
checks exhaustion before forming its address, and initializes every field.
The global array declarations and their chosen capacity are separate inputs;
this fragment has no dynamic allocator or byte arena. -/
namespace Rumoca.FMI3.StaticFactory
open CTree

def reserve : Stmt := .declare "size_t" "slot"
  (.call (.id CAtomicScan.function.signature.name)
    [.id "rumoca_instance_flags", .id "rumoca_instance_capacity"])

def exhausted : List Stmt := FactoryRejection.code "Instance capacity exhausted"

def guard : Stmt := .branch
  (.bin .eq (.id "slot") (.id "rumoca_instance_capacity")) exhausted []

def selectInstance : Stmt := .declare "Instance *" "m"
  (.address (.index (.id "rumoca_instances") (.id "slot")))

def initializeInstance (model : Solve.Model source) (kind : Kind) : List Stmt :=
  selectInstance :: InstanceSlot.code model kind

def code (model : Solve.Model source) (kind : Kind) : List Stmt :=
  reserve :: guard :: initializeInstance model kind

/-- Both public FMI factories share admission and the prepared Solve
initializer. Selecting storage introduces no source-language lowering. -/
def function (model : Solve.FMI3Model source) (kind : Kind) : Function :=
  ⟨FactoryArguments.signature kind, FactoryPrefix.body model kind (code model.solve kind), false⟩

end Rumoca.FMI3.StaticFactory
