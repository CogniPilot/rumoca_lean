import Rumoca.EFMIArchive
import Rumoca.EFMICheck
import Std.Time.Format

/-! Publish Algorithm Code or the complete tiny eFMU only after the fixed
actual-file checker accepts the staged bytes. Entropy, wall-clock accuracy,
file I/O and atomic rename remain external infrastructure. -/
namespace Rumoca.EFMIExport
open System FMI3.Package

/-- Candidate UUIDv4: RFC 9562 §5.4 version/variant bits, with the eFMI braces.
The OS supplies entropy; the actual-file certificate checks identity validity
and distinctness within this archive, not global uniqueness. -/
private def uuid : IO String := do
  let raw ← IO.getRandomBytes 16
  if raw.size != 16 then throw (IO.userError "Could not obtain eFMI identity bytes")
  let bytes := raw.set! 6 ((raw[6]! &&& 0x0f) ||| 0x40)
  let bytes := bytes.set! 8 ((bytes[8]! &&& 0x3f) ||| 0x80)
  let digits := (SHA1.hex bytes.data.toList).toList
  let fields := [(0, 8), (8, 4), (12, 4), (16, 4), (20, 12)]
  return "{" ++ String.intercalate "-" (fields.map fun (offset, width) =>
    String.ofList ((digits.drop offset).take width)) ++ "}"

private def identity : IO EFMI.Manifest.Identity := do
  let container ← uuid
  let algorithm ← uuid
  let production ← uuid
  let now ← Std.Time.Timestamp.now
  let generated := now.toPlainDateTimeAssumingUTC.format "uuuu-MM-dd'T'HH:mm:ss'Z'"
  return ⟨container, algorithm, production, generated⟩

def writeArchive (artifact : Artifact input) (output : FilePath) : IO Unit := do
  let workspace ← FMU.workspace
  let cwd ← IO.Process.getCurrentDir
  let destination := if output.isAbsolute then output else cwd / output
  let bytes ← match artifact.efmuArchive (← identity) with
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
    let log ← EFMICheck.run .efmi archiveFile sourceFile
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
    let log ← EFMICheck.run .algorithm algorithmFile sourceFile
    IO.FS.writeFile (staging / "kernel-audit.log") log
    let _ ← command "bash" #["scripts/audit-lean.sh", (staging / "kernel-audit.log").toString]
      (some workspace)
    IO.FS.rename algorithmFile destination
    IO.print log
    IO.println s!"Created checked Algorithm Code {destination}"
  finally IO.FS.removeDirAll staging

end Rumoca.EFMIExport
