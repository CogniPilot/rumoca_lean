import RumocaC.Interface
import RumocaEFMI.CHeader

/-! Bind the eFMI C type names to the actual interface declaration nodes.
The wrapper supplies its Model pointer spelling and the C double primitive;
real/status aliases are looked up in the emitted header declarations. -/
namespace Rumoca.EFMI
open CMemory
namespace CHeader

def Scalar.memoryType : Scalar → CType
  | .real64 => .float64
  | .status32 => .int32

/-- Lookup over actual emitted declaration nodes, used only by the target
contract. No source resolution or type inference is done in this backend. -/
def scalarNamed (name : String) : List Declaration → Option Scalar
  | [] => none
  | .alias scalar :: rest => if scalar.alias = name then some scalar else scalarNamed name rest
  | _ :: rest => scalarNamed name rest

def fieldsNamed (name : String) : List Declaration → Option (List Field)
  | [] => none
  | .structureType n fields :: rest => if n = name then some fields else fieldsNamed name rest
  | _ :: rest => fieldsNamed name rest

end CHeader

@[simp] def cConstants (name : String) : Option Value :=
  if name = "NULL" then some (.pointer none) else none

@[simp] def cTypes (type : String) : Option CType :=
  if type = "Model *" then some .pointer
  else if type = "double" then some .float64
  else (CHeader.scalarNamed type CHeader.declarations).map CHeader.Scalar.memoryType

abbrev cInterface : CInterface := { constants := cConstants, types := cTypes }

@[simp] theorem cInterface_types (name : String) :
    @CInterface.types cInterface name = cTypes name := rfl

@[simp] theorem cInterface_constants (name : String) :
    @CInterface.constants cInterface name = cConstants name := rfl

end Rumoca.EFMI
