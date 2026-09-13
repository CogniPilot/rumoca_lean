import RumocaFMI3.InstanceInitializationCode

/-! The reserved slot is stored before any handle escapes. Model and adapter
initialization reuse the existing prepared block; slot metadata is FMI-owned. -/
namespace Rumoca.FMI3.InstanceSlot
open CTree

def statement : Stmt := .assign (.field (.id "m") "slot" true) (.id "slot")

def code (model : Solve.Model source) (kind : Kind) : List Stmt :=
  statement :: InstanceInitialization.code model kind ++ [InstanceInitialization.returnHandle]

end Rumoca.FMI3.InstanceSlot
