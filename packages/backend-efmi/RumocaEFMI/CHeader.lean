import Std

/-! Explicit C declarations for the tiny eFMI interface. The manifest must
refer to these actual aliases and structure fields. A method returns a fixed
32-bit status; zero reports completion under the verified preconditions.
This does not add a GALEC error mode or a new source-language case. -/
namespace Rumoca.EFMI.CHeader

inductive Scalar where
  | real64 | status32
  deriving Repr, BEq, DecidableEq

def Scalar.alias : Scalar → String
  | .real64 => "EfmiReal"
  | .status32 => "EfmiStatus"

def Scalar.spelling : Scalar → String
  | .real64 => "double"
  | .status32 => "int32_t"

structure Field where
  name : String
  scalar : Scalar
  deriving Repr, BEq, DecidableEq

inductive Declaration where
  | alias (scalar : Scalar)
  | structureType (name : String) (fields : List Field)
  deriving Repr, BEq, DecidableEq

def statusName : String := "errorSignalStatus"
def stateFields : List Field :=
  [⟨"x", .real64⟩, ⟨"samplePeriod", .real64⟩, ⟨statusName, .status32⟩]
def declarations : List Declaration :=
  [.alias .real64, .alias .status32, .structureType "Model" stateFields]

def Declaration.render : Declaration → String
  | .alias scalar => "typedef " ++ scalar.spelling ++ " " ++ scalar.alias ++ ";\n"
  | .structureType name fields => "typedef struct {\n" ++
      String.join (fields.map fun field => "  " ++ field.scalar.alias ++ " " ++ field.name ++ ";\n") ++
      "} " ++ name ++ ";\n"

def render : String := String.join (declarations.map Declaration.render) ++ "\n"

end Rumoca.EFMI.CHeader
