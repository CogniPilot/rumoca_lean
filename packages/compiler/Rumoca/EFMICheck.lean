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
    (grammar galecGrammar : Option FilePath := none) : IO String := do
  let workspace ← FMU.workspace
  let input ← IO.FS.realPath input
  let source ← IO.FS.realPath source
  let grammar ← IO.FS.realPath (grammar.getD (workspace / "packages/modelica-parser/grammar/Modelica.ebnf"))
  let galecGrammar ← IO.FS.realPath (galecGrammar.getD (workspace / "packages/galec-parser/grammar/GALEC.ebnf"))
  let (entry, option, checker) ← match product with
    | .algorithm => pure ("CheckEFMIAlgorithm.lean", "algorithm", "Rumoca.EFMIArtifactCheck")
    | .efmi => do
      if ← input.isDir then
        pure ("CheckEFMIManifests.lean", "root", "Rumoca.EFMIManifestArtifactCheck")
      else
        pure ("CheckEFMIArchive.lean", "root", "Rumoca.EFMIArchiveArtifactCheck")
  -- `lake env lean` does not build imports. Ask Lake to bring the checker and
  -- its dependencies up to date, reusing its native module cache when possible.
  let _ ← FMI3.Package.command "lake" #["build", s!"rumoca_compiler/{checker}"] (some workspace)
  FMI3.Package.command "lake" #["env", "lean", "-s", "65536",
    s!"-Drumoca.efmi.source={source}", s!"-Drumoca.efmi.{option}={input}",
    s!"-Drumoca.efmi.grammar={grammar}", s!"-Drumoca.efmi.galecGrammar={galecGrammar}",
    ("packages/compiler/Tools/" ++ entry)] (some workspace)

end Rumoca.EFMICheck
