import Rumoca.TensorFMU

/-! Development command that assembles a tensor FMU from the array profile
through `compileTensor`, the tensor `writeSources`, the fixed tensor source-build
checker and the native archive step. This is not the CLI's production admission
path; the default compiler still rejects the array profile. -/
open Rumoca _root_.Parser

def main (args : List String) : IO Unit := do
  match args with
  | [sourcePath, output] =>
    let src ← IO.FS.readFile sourcePath
    let input : Source.InputRef := .single sourcePath src
    match compileTensor input with
    | .ok a => Rumoca.TensorFMU.build a output
    | .error e => throw (IO.userError s!"{e.phase}: {e.message}")
  | _ => throw (IO.userError "usage: tensor-fmu SOURCE OUTPUT.fmu")
