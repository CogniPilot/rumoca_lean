import RumocaC.Interface
import RumocaCore.Tensor

/-! Static declared-member metadata below expression evaluation. Logical shapes
and live object identities are explicit; storage validity is proved separately. -/
namespace Rumoca.CDeclaredMembers
open CMemory

structure Field where
  name : String
  spelling : String
  element : CType
  array : Option Tensor.Shape
  deriving DecidableEq, Repr

def Field.render (field : Field) : String :=
  "  " ++ field.spelling ++ " " ++ field.name ++
    (match field.array with | none => "" | some shape => "[" ++ toString shape.volume ++ "]") ++ ";\n"

structure Record where
  name : String
  fields : List Field
  deriving DecidableEq, Repr

def Record.render (record : Record) : String :=
  "typedef struct {\n" ++ String.join (record.fields.map Field.render) ++
    "} " ++ record.name ++ ";\n\n"

/-- Relate rendered element spellings to the supplied target dictionary. -/
def Record.Typed (record : Record) (interface : CInterface) : Prop :=
  ∀ field ∈ record.fields, interface.types field.spelling = some field.element

abbrev Declarations := String → Option (List Field)
abbrev Objects := Address → Option String

def fieldAt (declarations : Declarations) (objects : Objects) (base : Address) (name : String) : Option Field := do
  let record ← objects base
  let fields ← declarations record
  fields.find? (fun field => field.name == name)

def arrayAt (declarations : Declarations) (objects : Objects) (base : Address) (name : String) :
    Option Tensor.Shape := (fieldAt declarations objects base name).bind Field.array

/-- Scalar cells retain normal lvalue-to-rvalue conversion. An array member
instead supplies its first element address, without reading any element value. -/
def memberValue (declarations : Declarations) (objects : Objects) (heap : Heap)
    (base : Address) (name : String) : Option Value :=
  match arrayAt declarations objects base name with
  | some _ => some (.pointer (some (base.member name)))
  | none => load heap (base.member name)


end Rumoca.CDeclaredMembers
