import Rumoca.ConstantProduction
import Rumoca.FMU
import RumocaFMI3.Package
import RumocaFMI3.Header

/-! Development constant-rate FMU assembly. This mirrors the scalar `FMU` driver
and the tensor `TensorFMU` driver for the constant-rate profile, writing the same
FMU layout from the certified constant kernel C text, the rendered constant
adapter, the constant model description and the shared build description, then
running the fixed constant source-build checker and the native archive step. -/
namespace Rumoca.ConstantFMU
open System _root_.Parser
open Rumoca.FMI3 Rumoca.FMI3.Package

/-- The rendered constant adapter bytes for an artifact: the constant function
list over a scalar witness sharing the model name, using the pinned header
signatures. -/
def adapterBytes (a : ConstantArtifact input) (signatures : List CTree.Signature) :
    IO String := do
  match compile a.scalarInput with
  | .ok witness => return FMI3.ConstantFunctions.render witness.solve.prepareFMI3 a.constantModel signatures
  | .error e => throw (IO.userError s!"scalar witness compilation failed: {e.message}")

/-- Write the constant FMU sources in the same layout as the scalar driver. The
private kernel is the certified constant kernel text; the adapter is the rendered
constant function list; the model and build descriptions are the prepared
constant documents. -/
def writeSources (a : ConstantArtifact input) (root vendor : FilePath) : IO Unit := do
  let _ ← command "sha256sum" #["-c", "SHA256SUMS"] (some vendor)
  let signatures ← match Header.signatures (← IO.FS.readFile (vendor / "fmi3FunctionTypes.h")) with
    | .ok sigs => pure sigs
    | .error message => throw (IO.userError message)
  IO.FS.createDirAll (root / "sources")
  IO.FS.createDirAll (root / "documentation/licenses")
  IO.FS.createDirAll (root / "extra/org.cognipilot.rumoca")
  IO.FS.writeFile (root / "sources/model.c") ConstantKernel.modelC
  IO.FS.writeFile (root / "sources/fmi3.c") (← adapterBytes a signatures)
  IO.FS.writeFile (root / "modelDescription.xml")
    (XML.document (FMI3.TensorMetadata.constantModelDescription a.constantModel.shape a.constantModel.name))
  IO.FS.writeFile (root / "sources/buildDescription.xml")
    (XML.document (FMI3.Build.description a.name))
  IO.FS.writeFile (root / "documentation/index.html") Package.documentation
  IO.FS.writeFile (root / "documentation/licenses/fmi-standard.txt")
    (← IO.FS.readFile (vendor / "LICENSE.txt"))

/-- The fixed constant checker reads the staged kernel, adapter and XML bytes and
compiles the source with `compileConstant`. Producer-supplied proofs, native
compilation and ZIP validation cannot authorize this contract. -/
def checkSources (workspace root : FilePath) (sourceName : String) : IO Unit := do
  let extra := root / "extra/org.cognipilot.rumoca"
  let log ← command "lake" #["run", "verify-artifact", "constant-fmi3", root.toString, sourceName]
    (some workspace)
  IO.FS.writeFile (extra / "kernel-audit.log") log
  let _ ← command "bash" #["scripts/audit-lean.sh", (extra / "kernel-audit.log").toString] (some workspace)
  IO.FS.writeFile (extra / "lean-toolchain") (← IO.FS.readFile (workspace / "lean-toolchain"))
  IO.FS.writeFile (extra / "lake-manifest.json") (← IO.FS.readFile (workspace / "lake-manifest.json"))

/-- Assemble, check and validate a development constant-rate FMU. Unlike the
scalar production path this is a development artifact only; native compilation,
ZIP transport and the FMPy importer remain boundaries outside the proof model. -/
def build (a : ConstantArtifact input) (output : FilePath) : IO Unit := do
  let workspace ← FMU.workspace
  let cwd ← IO.Process.getCurrentDir
  let destination := if output.isAbsolute then output else cwd / output
  IO.FS.createDirAll (destination.parent.getD ".")
  let staging : FilePath := (← command "mktemp"
    #["-d", ((destination.parent.getD ".") / ".rumoca-constant-fmu.XXXXXX").toString]).trimAscii.toString
  try
    let root := staging / "content"
    let vendor := workspace / "packages/backend-fmi3/vendor/fmi3"
    IO.println "Preparing development constant-rate FMI 3 Model Exchange / Co-Simulation sources..."
    writeSources a root vendor
    IO.FS.writeFile (root / "extra/org.cognipilot.rumoca/Source.mo") input.source
    IO.println "Checking the constant numerical C, source-build recipe and FMI identities in Lean..."
    checkSources workspace root input.name
    IO.println "Building and validating the development constant-rate FMU..."
    let archive := staging / "model.fmu"
    FMI3.Package.archive a.name root vendor archive
    IO.FS.rename archive destination
    IO.println s!"Created {destination}"
  finally IO.FS.removeDirAll staging

end Rumoca.ConstantFMU
