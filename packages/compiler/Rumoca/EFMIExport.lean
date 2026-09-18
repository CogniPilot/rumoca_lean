import Rumoca.EFMIArchive
import Rumoca.EFMITensorArchive
import Rumoca.EFMICheck
import Rumoca.EFMIIdentity

/-! Publish Algorithm Code or the complete tiny eFMU only after the fixed
actual-file checker accepts the staged bytes. Entropy, wall-clock accuracy,
file I/O and atomic rename remain external infrastructure. -/
namespace Rumoca.EFMIExport
open System FMI3.Package

def writeArchive (artifact : Artifact input) (output : FilePath) : IO Unit := do
  let workspace ← FMU.workspace
  let cwd ← IO.Process.getCurrentDir
  let destination := if output.isAbsolute then output else cwd / output
  let identity ← EFMIIdentity.identity artifact.parsed.ast.name input.source
  let bytes ← match artifact.efmuArchive identity with
    | .ok bytes => pure bytes
    | .error error => throw (IO.userError error)
  IO.FS.createDirAll (destination.parent.getD ".")
  let staging : FilePath := (← command "mktemp"
    #["-d", ((destination.parent.getD ".") / ".rumoca-efmu.XXXXXX").toString]).trimAscii.toString
  try
    let sourceFile := staging / "Source.mo"
    let archiveFile := staging / "model.efmu"
    IO.FS.writeFile sourceFile input.source
    IO.FS.writeBinFile archiveFile bytes
    IO.eprintln "Checking the complete eFMU in Lean..."
    let log ← EFMICheck.run .efmi archiveFile sourceFile (sourceName := some input.name)
    IO.FS.writeFile (staging / "kernel-audit.log") log
    let _ ← command "bash" #["scripts/audit-lean.sh", (staging / "kernel-audit.log").toString]
      (some workspace)
    IO.FS.rename archiveFile destination
    IO.print log
    IO.eprintln s!"Created checked eFMU {destination}"
  finally IO.FS.removeDirAll staging

def writeAlgorithm (artifact : Artifact input) (output : FilePath) : IO Unit := do
  let workspace ← FMU.workspace
  let cwd ← IO.Process.getCurrentDir
  let destination := if output.isAbsolute then output else cwd / output
  IO.FS.createDirAll (destination.parent.getD ".")
  let staging : FilePath := (← command "mktemp"
    #["-d", ((destination.parent.getD ".") / ".rumoca-alg.XXXXXX").toString]).trimAscii.toString
  try
    let sourceFile := staging / "Source.mo"
    let algorithmFile := staging / "model.alg"
    IO.FS.writeFile sourceFile input.source
    IO.FS.writeFile algorithmFile artifact.algorithmSource
    let log ← EFMICheck.run .algorithm algorithmFile sourceFile (sourceName := some input.name)
    IO.FS.writeFile (staging / "kernel-audit.log") log
    let _ ← command "bash" #["scripts/audit-lean.sh", (staging / "kernel-audit.log").toString]
      (some workspace)
    IO.FS.rename algorithmFile destination
    IO.print log
    IO.println s!"Created checked Algorithm Code {destination}"
  finally IO.FS.removeDirAll staging

/-- Publish the pinned tensor square Algorithm Code, gated by the fixed
`tensor-algorithm` checker over the staged bytes. Mirrors `writeAlgorithm`: a
failed checker preserves any earlier published member and leaves no destination
or staging directory behind. -/
def writeTensorAlgorithm (_artifact : TensorArtifact input) (output : FilePath) : IO Unit := do
  let workspace ← FMU.workspace
  let cwd ← IO.Process.getCurrentDir
  let destination := if output.isAbsolute then output else cwd / output
  IO.FS.createDirAll (destination.parent.getD ".")
  let staging : FilePath := (← command "mktemp"
    #["-d", ((destination.parent.getD ".") / ".rumoca-tensor-alg.XXXXXX").toString]).trimAscii.toString
  try
    let sourceFile := staging / "Source.mo"
    let algorithmFile := staging / "model.alg"
    IO.FS.writeFile sourceFile input.source
    IO.FS.writeFile algorithmFile EFMI.tensorUnitSource
    let log ← EFMICheck.run .tensorAlgorithm algorithmFile sourceFile (sourceName := some input.name)
    IO.FS.writeFile (staging / "kernel-audit.log") log
    let _ ← command "bash" #["scripts/audit-lean.sh", (staging / "kernel-audit.log").toString]
      (some workspace)
    IO.FS.rename algorithmFile destination
    IO.print log
    IO.println s!"Created checked tensor Algorithm Code {destination}"
  finally IO.FS.removeDirAll staging

/-- Publish the frozen tensor eFMU, gated by the fixed `tensor-efmi-archive`
checker over the staged bytes. Mirrors `writeArchive` including its
failure-preservation behavior. -/
def writeTensorArchive (artifact : TensorArtifact input) (output : FilePath) : IO Unit := do
  let workspace ← FMU.workspace
  let cwd ← IO.Process.getCurrentDir
  let destination := if output.isAbsolute then output else cwd / output
  let identity ← EFMIIdentity.identity artifact.name input.source
  let bytes ← match artifact.efmuArchive identity with
    | .ok bytes => pure bytes
    | .error error => throw (IO.userError error)
  IO.FS.createDirAll (destination.parent.getD ".")
  let staging : FilePath := (← command "mktemp"
    #["-d", ((destination.parent.getD ".") / ".rumoca-tensor-efmu.XXXXXX").toString]).trimAscii.toString
  try
    let sourceFile := staging / "Source.mo"
    let archiveFile := staging / "model.efmu"
    IO.FS.writeFile sourceFile input.source
    IO.FS.writeBinFile archiveFile bytes
    IO.eprintln "Checking the complete tensor eFMU in Lean..."
    let log ← EFMICheck.run .tensorEfmi archiveFile sourceFile (sourceName := some input.name)
    IO.FS.writeFile (staging / "kernel-audit.log") log
    let _ ← command "bash" #["scripts/audit-lean.sh", (staging / "kernel-audit.log").toString]
      (some workspace)
    IO.FS.rename archiveFile destination
    IO.print log
    IO.eprintln s!"Created checked tensor eFMU {destination}"
  finally IO.FS.removeDirAll staging

end Rumoca.EFMIExport
