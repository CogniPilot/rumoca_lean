import Rumoca.ConstantFMU

/-! Development command that assembles a constant-rate FMU from the constant
profile through `compileConstant`, the constant `writeSources`, the fixed constant
source-build checker and the native archive step. This is not the CLI's production
admission path; the default compiler still rejects the constant profile. -/
open Rumoca _root_.Parser

def main (args : List String) : IO Unit := do
  match args with
  | [sourcePath, output] =>
    let src ← IO.FS.readFile sourcePath
    let input : Source.InputRef := .single sourcePath src
    match compileConstant input with
    | .ok a => Rumoca.ConstantFMU.build a output
    | .error e => throw (IO.userError s!"{e.phase}: {e.message}")
  | _ => throw (IO.userError "usage: constant-fmu SOURCE OUTPUT.fmu")
