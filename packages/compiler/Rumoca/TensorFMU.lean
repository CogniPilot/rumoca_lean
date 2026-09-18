import Rumoca.TensorProduction
import Rumoca.FMU
import RumocaFMI3.Package
import RumocaFMI3.Header

/-! Development tensor FMU assembly. This mirrors the scalar `FMU` driver for the
pointwise tensor profile, writing the same FMU layout from the certified tensor
kernel C text, the rendered tensor adapter, the tensor model description and the
shared build description, then running the fixed tensor source-build checker and
the native archive step. It is a development command, not the CLI's production
admission path. -/
namespace Rumoca.TensorFMU
open System _root_.Parser
open Rumoca.FMI3 Rumoca.FMI3.Package

/-- The rendered tensor adapter bytes for an artifact: the tensor function list
over a scalar witness sharing the model name, using the pinned header
signatures. -/
def adapterBytes (a : TensorArtifact input) (signatures : List CTree.Signature) :
    IO String := do
  match compile a.scalarInput with
  | .ok witness => return FMI3.TensorFunctions.render witness.solve.prepareFMI3 a.tensorModel signatures
  | .error e => throw (IO.userError s!"scalar witness compilation failed: {e.message}")

/-- Write the tensor FMU sources in the same layout as the scalar driver. The
private kernel is the certified tensor kernel text; the adapter is the rendered
tensor function list; the model and build descriptions are the prepared tensor
documents. -/
def writeSources (a : TensorArtifact input) (root vendor : FilePath) : IO Unit := do
  let _ ← command "sha256sum" #["-c", "SHA256SUMS"] (some vendor)
  let signatures ← match Header.signatures (← IO.FS.readFile (vendor / "fmi3FunctionTypes.h")) with
    | .ok sigs => pure sigs
    | .error message => throw (IO.userError message)
  IO.FS.createDirAll (root / "sources")
  IO.FS.createDirAll (root / "documentation/licenses")
  IO.FS.createDirAll (root / "extra/org.cognipilot.rumoca")
  IO.FS.writeFile (root / "sources/model.c") TensorKernel.modelC
  IO.FS.writeFile (root / "sources/fmi3.c") (← adapterBytes a signatures)
  IO.FS.writeFile (root / "modelDescription.xml")
    (XML.document (FMI3.TensorMetadata.modelDescription a.tensorModel))
  IO.FS.writeFile (root / "sources/buildDescription.xml")
    (XML.document (FMI3.Build.description a.name))
  IO.FS.writeFile (root / "documentation/index.html") Package.documentation
  IO.FS.writeFile (root / "documentation/licenses/fmi-standard.txt")
    (← IO.FS.readFile (vendor / "LICENSE.txt"))

/-- The fixed tensor checker reads the staged kernel, adapter and XML bytes and
compiles the source with `compileTensor`. Producer-supplied proofs, native
compilation and ZIP validation cannot authorize this contract. -/
def checkSources (workspace root : FilePath) (sourceName : String) : IO Unit := do
  let extra := root / "extra/org.cognipilot.rumoca"
  let log ← command "lake" #["run", "verify-artifact", "tensor-fmi3", root.toString, sourceName]
    (some workspace)
  IO.FS.writeFile (extra / "kernel-audit.log") log
  let _ ← command "bash" #["scripts/audit-lean.sh", (extra / "kernel-audit.log").toString] (some workspace)
  IO.FS.writeFile (extra / "lean-toolchain") (← IO.FS.readFile (workspace / "lean-toolchain"))
  IO.FS.writeFile (extra / "lake-manifest.json") (← IO.FS.readFile (workspace / "lake-manifest.json"))

/-- Assemble, check and validate a development tensor FMU. Unlike the scalar
production path this is a development artifact only; native compilation, ZIP
transport and the FMPy importer remain boundaries outside the proof model. -/
def build (a : TensorArtifact input) (output : FilePath) : IO Unit := do
  let workspace ← FMU.workspace
  let cwd ← IO.Process.getCurrentDir
  let destination := if output.isAbsolute then output else cwd / output
  IO.FS.createDirAll (destination.parent.getD ".")
  let staging : FilePath := (← command "mktemp"
    #["-d", ((destination.parent.getD ".") / ".rumoca-tensor-fmu.XXXXXX").toString]).trimAscii.toString
  try
    let root := staging / "content"
    let vendor := workspace / "packages/backend-fmi3/vendor/fmi3"
    IO.println "Preparing development tensor FMI 3 Model Exchange / Co-Simulation sources..."
    writeSources a root vendor
    IO.FS.writeFile (root / "extra/org.cognipilot.rumoca/Source.mo") input.source
    IO.println "Checking the tensor numerical C, source-build recipe and FMI identities in Lean..."
    checkSources workspace root input.name
    IO.println "Building and validating the development tensor FMU..."
    let archive := staging / "model.fmu"
    FMI3.Package.archive a.name root vendor archive
    IO.FS.rename archive destination
    IO.println s!"Created {destination}"
  finally IO.FS.removeDirAll staging

end Rumoca.TensorFMU
