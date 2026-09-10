import RumocaFMI3.Runtime
import RumocaC.Codegen

/-! Host build orchestration. These operations are checked by independent
artifact and importer tests; they are not Lean proofs of the native toolchain. -/
namespace Rumoca.FMI3.Package
open System

def command (cmd : String) (args : Array String) (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO String := do
  let result ← IO.Process.output { cmd, args, cwd, env }
  if result.exitCode != 0 then
    throw (IO.userError s!"{cmd} failed ({result.exitCode}):\n{result.stdout}{result.stderr}")
  return result.stdout

def documentation : String :=
  "<!doctype html><html lang=\"en\"><meta charset=\"utf-8\"><title>Rumoca unit FMU</title>" ++
  "<h1>Rumoca unit FMU</h1><p>FMI 3.0 Model Exchange and Co-Simulation share one continuous state. " ++
  "The model equation is der(x)=1; the state name comes from the Modelica source. " ++
  "The state is local, with default start 0; the importer may set a finite Float64 start value.</p>" ++
  "<p>ME delegates integration to the importer. CS embeds the unit Euler policy: " ++
  "each internal step calls the same numerical kernel, with binary64 nearest-even rounding. " ++
  "Communication steps must be positive integer multiples of the internal step 1, " ++
  "at most 1000000 per call. Unsupported steps return Discard without advancing. " ++
  "There are no events, inputs, state serialization, clocks, or intermediate updates.</p>" ++
  "<p>sources/model.c has an actual-file Lean certificate of source-to-C numerical semantic " ++
  "preservation, including all finite binary64 starts. The source-build description is also " ++
  "checked against its declared compiler, flags, sources and library requirements. " ++
  "The FMI adapter, model-description XML, ZIP, native " ++
  "C compilation, linking, callbacks, and host solver are outside that theorem. " ++
  "Their validation is not a proof of full FMI compliance. " ++
  "See extra/org.cognipilot.rumoca for the source snapshot and kernel checking log.</p>" ++
  "<p>The shared library targets the platform named in binaries/. The build description " ++
  "declares Linux x86_64/aarch64 GCC source profiles, including the system math library. " ++
  "Use the FMI 3 headers supplied by your importer. Other source-build platforms require " ++
  "a separately validated build profile. Execution requires IEEE binary64, gradual " ++
  "underflow and round-to-nearest; compiler flags do not establish these host conditions.</p></html>\n"

/-- Write only data prepared by Solve, and the existing C lowering of that Solve
program. The driver must check sources/model.c before invoking archive. -/
def writeSources (m : Solve.FMI3Model source) (root vendor : FilePath) : IO Unit := do
  let _ ← command "sha256sum" #["-c", "SHA256SUMS"] (some vendor)
  let sigs ← match Header.signatures (← IO.FS.readFile (vendor / "fmi3FunctionTypes.h")) with
    | .ok sigs => pure sigs
    | .error message => throw (IO.userError message)
  IO.FS.createDirAll (root / "sources")
  IO.FS.createDirAll (root / "documentation/licenses")
  IO.FS.createDirAll (root / "extra/org.cognipilot.rumoca")
  IO.FS.writeFile (root / "sources/model.c") (C.render (C.lower m.solve))
  IO.FS.writeFile (root / "sources/fmi3.c") (Runtime.render m sigs)
  IO.FS.writeFile (root / "modelDescription.xml") (XML.document (modelDescription m))
  IO.FS.writeFile (root / "sources/buildDescription.xml") (XML.document Build.description)
  IO.FS.writeFile (root / "documentation/index.html") documentation
  IO.FS.writeFile (root / "documentation/licenses/fmi-standard.txt")
    (← IO.FS.readFile (vendor / "LICENSE.txt"))

def hostPlatform : IO Build.Platform := do
  let os := (← command "uname" #["-s"]).trimAscii.toString
  let arch := (← command "uname" #["-m"]).trimAscii.toString
  if os != "Linux" || !(arch == "x86_64" || arch == "aarch64") then
    throw (IO.userError s!"FMU binary build currently supports Linux x86_64/aarch64; host is {os}/{arch}")
  return if arch == "x86_64" then .x86_64Linux else .aarch64Linux

/-- Compile and validate in a private staging directory. Publication is left to
the driver so failure cannot replace an earlier successful FMU. -/
def archive (root vendor destination : FilePath) : IO Unit := do
  let platform ← hostPlatform
  IO.FS.createDirAll (root / "binaries" / platform.name)
  let library := root / "binaries" / platform.name / (modelIdentifier ++ ".so")
  let invocation := Build.invocation platform (root / "sources").toString vendor.toString library.toString
  let _ ← command invocation.compiler invocation.args.toArray
  let _ ← command "zip" #["-q", "-X", "-0", "-r", destination.toString,
    "modelDescription.xml", "sources", "binaries", "documentation", "extra"] (some root)
  let _ ← command "unzip" #["-tqq", destination.toString]
  let _ ← command "fmpy" #["validate", destination.toString]
  pure ()

end Rumoca.FMI3.Package
