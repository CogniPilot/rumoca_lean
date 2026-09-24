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

def exhaustedWith (pointerPresent : Expr → Expr) : List Stmt := FactoryRejection.codeWith pointerPresent "Instance capacity exhausted"

def guardWith (pointerPresent : Expr → Expr) : Stmt := .branch
  (.bin .eq (.id "slot") (.id "rumoca_instance_capacity")) (exhaustedWith pointerPresent) []

def selectInstance : Stmt := .declare "Instance *" "m"
  (.address (.index (.id "rumoca_instances") (.id "slot")))

def initializeInstance (model : Solve.Model source) (kind : Kind) : List Stmt :=
  selectInstance :: InstanceSlot.code model kind

def codeWith (pointerPresent : Expr → Expr) (model : Solve.Model source) (kind : Kind) : List Stmt :=
  reserve :: guardWith pointerPresent :: initializeInstance model kind

/-- Both public FMI factories share admission and the prepared Solve
initializer. Selecting storage introduces no source-language lowering. -/
def functionWith (pointerPresent : Expr → Expr) (model : Solve.FMI3Model source) (kind : Kind) : Function :=
  ⟨FactoryArguments.signature kind, FactoryPrefix.bodyWith pointerPresent model kind (codeWith pointerPresent model.solve kind), false⟩

def logicalExhausted : List Stmt := exhaustedWith id
def logicalGuard : Stmt := guardWith id
def logicalCode (model : Solve.Model source) (kind : Kind) : List Stmt := codeWith id model kind
def logicalFunction (model : Solve.FMI3Model source) (kind : Kind) : Function := functionWith id model kind
def exhausted : List Stmt := exhaustedWith FactoryRejection.explicitPresent
def guard : Stmt := guardWith FactoryRejection.explicitPresent
def code (model : Solve.Model source) (kind : Kind) : List Stmt :=
  codeWith FactoryRejection.explicitPresent model kind
def function (model : Solve.FMI3Model source) (kind : Kind) : Function :=
  functionWith FactoryRejection.explicitPresent model kind

end Rumoca.FMI3.StaticFactory
