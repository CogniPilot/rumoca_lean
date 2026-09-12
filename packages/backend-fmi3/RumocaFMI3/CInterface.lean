import RumocaC.Interface

/-! Constants and typedef spellings supplied by the FMI 3 C interface. These
are explicit inputs to shared C semantics, not global C language builtins. -/
namespace Rumoca.FMI3

/-- Supplied static addresses for parameterizing FMI proofs. This makes no
allocation or storage-validity claim; those are separate heap obligations. -/
class StaticLiterals where
  addresses : CLiteralAddresses

@[simp] def cConstants : String → Option CMemory.Value
  | "fmi3OK" => some (.integer 0)
  | "fmi3Warning" => some (.integer 1)
  | "fmi3Discard" => some (.integer 2)
  | "fmi3Error" => some (.integer 3)
  | "fmi3Fatal" => some (.integer 4)
  | "NULL" => some (.pointer none)
  | _ => none

/-- Types required by the pinned API's adjusted parameters and the current
runtime bodies. Pointer values are opaque symbolic addresses here: this does
not establish pointee layouts, callback execution or the native ABI. -/
@[simp] def cTypes (type : String) : Option CMemory.CType :=
  if ["Instance *", "Model *", "const Model *", "fmi3Instance",
      "fmi3Float64 *", "const fmi3Float64 *", "const char *", "fmi3String",
      "fmi3InstanceEnvironment", "fmi3FMUState", "fmi3LogMessageCallback",
      "fmi3ClockUpdateCallback", "fmi3IntermediateUpdateCallback",
      "fmi3LockPreemptionCallback", "fmi3UnlockPreemptionCallback",
      "const fmi3String *", "const fmi3ValueReference *",
      "fmi3Float32 *", "fmi3Int8 *", "fmi3UInt8 *", "fmi3Int16 *", "fmi3UInt16 *",
      "fmi3Int32 *", "fmi3UInt32 *", "fmi3Int64 *", "fmi3UInt64 *", "fmi3Boolean *",
      "fmi3String *", "size_t *", "fmi3Binary *", "fmi3Clock *",
      "const fmi3Float32 *", "const fmi3Int8 *", "const fmi3UInt8 *",
      "const fmi3Int16 *", "const fmi3UInt16 *", "const fmi3Int32 *", "const fmi3UInt32 *",
      "const fmi3Int64 *", "const fmi3UInt64 *", "const fmi3Boolean *",
      "const size_t *", "const fmi3Binary *", "const fmi3Clock *",
      "fmi3ValueReference *", "fmi3DependencyKind *", "fmi3FMUState *",
      "fmi3Byte *", "const fmi3Byte *", "fmi3IntervalQualifier *"].contains type then some .pointer
  else if type = "double" || type = "fmi3Float64" then some .float64
  else if type = "size_t" || type = "uint64_t" then some .size
  else if type = "int" || type = "fmi3Status" then some .int32
  else if type = "fmi3Boolean" then some .boolean
  else if type = "fmi3ValueReference" then some (.unsigned 32)
  else none

abbrev cInterface (literals : CLiteralAddresses := fun _ => none) : CInterface :=
  { constants := cConstants, types := cTypes, literals }

@[simp] theorem cInterface_types (literals : CLiteralAddresses) (name : String) :
    @CInterface.types (cInterface literals) name = cTypes name := rfl

@[simp] theorem cInterface_constants (literals : CLiteralAddresses) (name : String) :
    @CInterface.constants (cInterface literals) name = cConstants name := rfl

@[simp] theorem cInterface_literals (literals : CLiteralAddresses) (source : String) :
    @CInterface.literals (cInterface literals) source = literals source := rfl

end Rumoca.FMI3
