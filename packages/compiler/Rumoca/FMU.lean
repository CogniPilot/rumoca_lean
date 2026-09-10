import Rumoca.Compiler
import RumocaFMI3.Package

open _root_.Parser

namespace Rumoca.FMU
open System FMI3.Package

private def findRoot (start : FilePath) : IO FilePath := do
  let mut path := start
  for _ in [:16] do
    if ← (path / "packages/compiler/Tools/CheckArtifact.lean").pathExists then
      return path
    let some parent := path.parent | break
    if parent == path then break
    path := parent
  throw (IO.userError "Cannot find Rumoca workspace; run from the workspace or set RUMOCA_ROOT")

def workspace : IO FilePath := do
  if let some root ← IO.getEnv "RUMOCA_ROOT" then return ← IO.FS.realPath root
  try findRoot (← IO.Process.getCurrentDir)
  catch _ => findRoot (← IO.appPath)

/-- The fixed checker reads the staged source, kernel and build-description bytes.
Producer-supplied proofs, native compilation and ZIP validation cannot authorize
this contract. -/
def checkSources (workspace root : FilePath) : IO Unit := do
  let extra := root / "extra/org.cognipilot.rumoca"
  let log ← command "lake" #["env", "lean", s!"-Drumoca.fmi3.root={root}",
    "packages/compiler/Tools/CheckFMI3Build.lean"] (some workspace)
  IO.FS.writeFile (extra / "kernel-audit.log") log
  let _ ← command "bash" #["scripts/audit-lean.sh", (extra / "kernel-audit.log").toString] (some workspace)
  IO.FS.writeFile (extra / "lean-toolchain") (← IO.FS.readFile (workspace / "lean-toolchain"))
  IO.FS.writeFile (extra / "lake-manifest.json") (← IO.FS.readFile (workspace / "lake-manifest.json"))

def build (source : String) (artifact : Artifact source) (output : FilePath) : IO Unit := do
  let workspace ← workspace
  let cwd ← IO.Process.getCurrentDir
  let destination := if output.isAbsolute then output else cwd / output
  IO.FS.createDirAll (destination.parent.getD ".")
  let staging : FilePath := (← command "mktemp"
    #["-d", ((destination.parent.getD ".") / ".rumoca-fmu.XXXXXX").toString]).trimAscii.toString
  try
    let root := staging / "content"
    let vendor := workspace / "packages/backend-fmi3/vendor/fmi3"
    IO.println "Preparing FMI 3 Model Exchange / Co-Simulation sources..."
    FMI3.Package.writeSources artifact.solve.prepareFMI3 root vendor
    IO.FS.writeFile (root / "extra/org.cognipilot.rumoca/Source.mo") source
    IO.println "Checking the actual numerical C and source-build description in Lean..."
    checkSources workspace root
    IO.println "Building and validating the FMU..."
    let archive := staging / "model.fmu"
    FMI3.Package.archive root vendor archive
    IO.FS.rename archive destination
    IO.println s!"Created {destination}"
  finally IO.FS.removeDirAll staging

end Rumoca.FMU
