/-! Structured declarations for permanent C storage. Record members retain
their declaration order, and arrays retain their bound rather than enumerating
elements. Type spellings, C constraints and storage interpretation are checked
by separate contracts. There is no source-name resolution or IR lowering here. -/
namespace Rumoca.CObject

structure Field where
  type : String
  name : String
  deriving DecidableEq, Repr

def Field.render (field : Field) : String := field.type ++ " " ++ field.name ++ ";"

structure Record where
  name : String
  fields : List Field
  deriving DecidableEq, Repr

def Record.render (record : Record) : String :=
  "typedef struct {\n" ++ String.join (record.fields.map fun field => "  " ++ field.render ++ "\n") ++
    "} " ++ record.name ++ ";\n"

structure StaticArray where
  type : String
  name : String
  count : Nat
  deriving DecidableEq, Repr

def StaticArray.render (array : StaticArray) : String :=
  "static " ++ array.type ++ " " ++ array.name ++ "[" ++ toString array.count ++ "];\n"

structure Constant where
  type : String
  name : String
  value : Nat
  deriving DecidableEq, Repr

def Constant.render (constant : Constant) : String :=
  "static const " ++ constant.type ++ " " ++ constant.name ++ " = " ++ toString constant.value ++ ";\n"

end Rumoca.CObject
