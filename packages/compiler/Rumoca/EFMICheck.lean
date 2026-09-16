import Rumoca.FMU

open _root_.Parser

/-! Thin process interface to the fixed kernel checking entry points. Paths
are resolved before changing to the compiler workspace. Arguments are passed
directly to the process API, never interpolated into a shell command. -/
namespace Rumoca.EFMICheck
open System

inductive Product where
  | algorithm
  | efmi

def run (product : Product) (input source : FilePath)
    (grammar galecGrammar : Option FilePath := none) (sourceName : Option String := none) : IO String := do
  let name := sourceName.getD source.toString
  let workspace ← FMU.workspace
  let input ← IO.FS.realPath input
  let source ← IO.FS.realPath source
  let grammar ← IO.FS.realPath (grammar.getD (workspace / "packages/modelica-parser/grammar/Modelica.ebnf"))
  let galecGrammar ← IO.FS.realPath (galecGrammar.getD (workspace / "packages/galec-parser/grammar/GALEC.ebnf"))
  let kind : String ← match product with
    | .algorithm => pure "algorithm"
    | .efmi => do if ← input.isDir then pure "efmi-directory" else pure "efmi-archive"
  -- The native Lake job builds imports and traces the actual bytes, including
  -- both grammars. Its product is the checked .olean, never a producer's proof.
  FMI3.Package.command "lake" #["run", "verify-artifact", kind, source.toString,
    input.toString, grammar.toString, galecGrammar.toString, name]
    (some workspace)

end Rumoca.EFMICheck
