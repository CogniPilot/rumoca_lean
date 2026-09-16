import Lake
import Lake.CLI.Build
open Lake DSL

package lean_rumoca where
  version := v!"0.1.0"

require rumoca_compiler from "packages/compiler"
require rumoca_fmu_runner from "packages/fmu-runner"
require rumoca_lsp from "packages/lsp"

-- Delegate workspace builds to package products without redeclaring their
-- libraries or executables here.
@[default_target]
target all _pkg : Unit := do
  let mut jobs := #[]
  for packageName in #[`rumoca_compiler, `rumoca_fmu_runner, `rumoca_lsp] do
    let some pkg := (← getWorkspace).findPackageByName? packageName
      | error s!"missing package: {packageName}"
    for name in pkg.defaultTargets do
      if let some lib := pkg.findLeanLib? name then
        jobs := jobs.push (← (lib.facetCore LeanLib.defaultFacet).fetch).toOpaque
      else if let some exe := pkg.findLeanExe? name then
        jobs := jobs.push (← exe.exe.fetch).toOpaque
      else
        error s!"unsupported default target: {name}"
  return Job.mixArray jobs

-- Aggregate the packages' own targets through Lake's native dependency graph.
-- No proof implementation or separate cache lives in this coordinating file.
private def fetchTargets (targets : List String) : FetchM (Job Unit) := do
  let specs ← (parseTargetSpecs (← getWorkspace) targets).toIO
    (fun e => IO.userError (toString e))
  buildSpecs specs

target «check-parser» _pkg : Unit :=
  fetchTargets ["parser/Parser", "parser/ParserChecks"]

target «check-modelica-parser» _pkg : Unit :=
  fetchTargets ["modelica_parser/ModelicaParser", "modelica_parser/ModelicaParserChecks"]

target «check-galec-parser» _pkg : Unit :=
  fetchTargets ["galec_parser/GALECParser", "galec_parser/GALECParserChecks"]

target «check-lsp» _pkg : Unit :=
  fetchTargets ["rumoca_lsp/RumocaLSP", "rumoca_lsp/RumocaLSPChecks"]

target «check-core» _pkg : Unit :=
  fetchTargets ["rumoca_core/RumocaCore", "rumoca_core/RumocaCoreChecks"]

target «check-c» _pkg : Unit :=
  fetchTargets ["rumoca_c/RumocaC", "rumoca_c/RumocaCChecks"]

target «check-fmi3» _pkg : Unit :=
  fetchTargets ["rumoca_fmi3/RumocaFMI3", "rumoca_fmi3/RumocaFMI3Checks"]

target «check-efmi» _pkg : Unit :=
  fetchTargets ["rumoca_efmi/RumocaEFMI", "rumoca_efmi/RumocaEFMIChecks"]

target «check-sha1» _pkg : Unit :=
  fetchTargets ["sha1/SHA1", "sha1/SHA1Checks"]

target «check-xml» _pkg : Unit :=
  fetchTargets ["xml/XML", "xml/XMLChecks"]

target «check-compiler» _pkg : Unit :=
  fetchTargets ["rumoca_compiler/Rumoca", "rumoca_compiler/RumocaCompilerChecks"]

target «check-packages» _pkg : Unit :=
  fetchTargets ["parser/Parser", "modelica_parser/ModelicaParser", "galec_parser/GALECParser", "rumoca_core/RumocaCore", "rumoca_c/RumocaC",
    "rumoca_fmi3/RumocaFMI3", "sha1/SHA1", "xml/XML", "rumoca_efmi/RumocaEFMI",
    "rumoca_compiler/Rumoca", "rumoca_fmu_runner", "rumoca_lsp/RumocaLSP"]

target audit _pkg : Unit :=
  fetchTargets ["proof_audit/ProofAuditChecks", "parser/ParserChecks",
    "modelica_parser/ModelicaParserChecks", "galec_parser/GALECParserChecks",
    "rumoca_core/RumocaCoreChecks", "rumoca_c/RumocaCChecks", "rumoca_fmi3/RumocaFMI3Checks", "sha1/SHA1Checks",
    "xml/XMLChecks", "rumoca_efmi/RumocaEFMIChecks", "rumoca_compiler/RumocaCompilerChecks",
    "rumoca_lsp/RumocaLSPChecks"]

private def buildTargets (targets : List String) : ScriptM Unit :=
  runBuild (fetchTargets targets)

private def command (cmd : String) (args : Array String := #[]) : ScriptM Unit := do
  let child ← IO.Process.spawn {
    cmd, args, cwd := some (← getRootPackage).dir
    stdin := .inherit, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do
    throw (IO.userError s!"{cmd} failed with exit code {code}")

private def noArgs (args : List String) : ScriptM Unit := do
  unless args.isEmpty do throw (IO.userError "this command takes no arguments")

private structure CertificateOutputs where
  object : System.FilePath
  audit : System.FilePath
  identityFile : System.FilePath
  identity : ByteArray
  inputs : Array (System.FilePath × ByteArray)

-- Actual artifacts are untrusted inputs. Lake's freshness hash selects a build
-- product; exact snapshot equality binds that product to the current files.
private def CertificateOutputs.matches (out : CertificateOutputs) : IO Bool := do
  unless (← out.object.pathExists) && (← out.audit.pathExists) do return false
  unless (← IO.FS.readBinFile out.identityFile) == out.identity do return false
  for (path, bytes) in out.inputs do
    unless (← IO.FS.readBinFile path) == bytes do return false
  return true

private instance : CheckExists CertificateOutputs where
  checkExists out := do return (← out.matches.toBaseIO).toOption.getD false

private instance : GetMTime CertificateOutputs where
  getMTime out := do return min (← getMTime out.object) (← getMTime out.audit)

private structure CertificateRequest where
  kind : String
  sourceName : String
  entry : System.FilePath
  inputs : Array System.FilePath
  options : Array String
  env : Array (String × Option String) := #[]

private def certificateJob (request : CertificateRequest) : FetchM (Job System.FilePath) :=
  withRegisterJob s!"certificate {request.kind}" do
  let workspace ← getWorkspace
  let some compiler := workspace.findPackageByName? `rumoca_compiler
    | error "missing compiler package"
  let mut deps := #[]
  -- Parse the fixed entry point's real imports; additions cannot evade the trace.
  let header ← Lean.parseImports' (← IO.FS.readFile request.entry) request.entry.toString
  for imp in header.imports do
    if let some mod := workspace.findModule? imp.module then
      deps := deps.push (← mod.leanArts.fetch).toOpaque
    else if !(imp.module == `Init || imp.module == `Lean || imp.module == `Std) then
      error s!"untracked certificate import: {imp.module}"
  for path in request.inputs do
    let job ← inputBinFile path
    deps := deps.push job.toOpaque
  for path in #[request.entry, "lakefile.lean"] do
    deps := deps.push (← inputBinFile path).toOpaque
  (Job.mixArray deps).mapM fun _ => do
    addLeanTrace
    addPlatformTrace
    -- File locations are I/O routing, except the source identity quoted into
    -- the theorem. Input bytes are traced in a fixed, role-sensitive order.
    addPureTrace #[request.kind, request.sourceName] "certificate identity"
    let trace ← getTrace
    let directory := compiler.buildDir / "certificates" / request.kind / trace.hash.toString
    let objectName := (request.entry.withExtension "olean").fileName.getD "Certificate.olean"
    let inputBytes ← (request.inputs.mapM IO.FS.readBinFile : IO (Array ByteArray))
    let identity := Lean.toJson #[request.kind, request.sourceName] |>.compress.toUTF8
    let outputs : CertificateOutputs := {
      object := directory / objectName, audit := directory / "audit.log",
      identityFile := directory / "identity.json", identity,
      inputs := inputBytes.mapIdx fun i bytes => (directory / s!"input-{i}.bin", bytes) }
    let traceFile := directory / "Certificate.trace"
    buildUnlessUpToDate outputs trace traceFile do
      IO.FS.createDirAll directory
      removeFileIfExists traceFile
      removeFileIfExists outputs.object
      removeFileIfExists outputs.audit
      -- Lake supplies an explicit import-artifact map (--setup), so the
      -- checker loads the same modules whose native jobs are dependencies.
      let invocation ← (← prepareLeanCommand request.entry (#["-s", "65536",
        "-R", (request.entry.parent.getD ".").toString, "-o", outputs.object.toString,
        s!"-Drumoca.certificate.sourceName={request.sourceName}"] ++ request.options)).await
      let result ← IO.Process.output { invocation with
        env := invocation.env ++ request.env
        cwd := workspace.root.dir }
      unless result.exitCode == 0 do
        -- A failed run retains no product; do not leave an empty directory.
        IO.FS.removeDirAll directory
        error (result.stdout ++ result.stderr)
      IO.FS.writeFile outputs.audit (result.stdout ++ result.stderr)
      IO.FS.writeBinFile outputs.identityFile outputs.identity
      for (path, bytes) in outputs.inputs do IO.FS.writeBinFile path bytes
    -- Publication must not use a trace computed before a concurrent file edit.
    for path in request.inputs, before in inputBytes do
      unless (← IO.FS.readBinFile path) == before do
        removeFileIfExists traceFile
        error s!"verification input changed during certification: {path}"
    return outputs.audit

private def certificateRequest (args : List String) : IO CertificateRequest := do
  let tools : System.FilePath := "packages/compiler/Tools"
  let mGrammar : System.FilePath := "packages/modelica-parser/grammar/Modelica.ebnf"
  match args with
  | ["c", source, output, grammar] => do
    return {
      kind := "c", sourceName := source, entry := tools / "CheckArtifact.lean",
      inputs := #[source, output, grammar].map System.FilePath.mk, options := #[],
      env := #[("RUMOCA_SOURCE", some source), ("RUMOCA_C", some output), ("RUMOCA_GRAMMAR", some grammar)] }
  | "fmi3" :: root :: names => do
    let directory : System.FilePath := root
    let source := directory / "extra/org.cognipilot.rumoca/Source.mo"
    let name ← match names with
      | [] => pure source.toString
      | [name] => pure name
      | _ => throw (IO.userError "expected fmi3 ROOT [SOURCE_NAME]")
    return {
      kind := "fmi3", sourceName := name, entry := tools / "CheckFMI3Build.lean",
      inputs := #[source, directory / "sources/model.c", directory / "sources/fmi3.c",
        directory / "sources/buildDescription.xml", directory / "modelDescription.xml", mGrammar,
        "packages/backend-fmi3/vendor/fmi3/fmi3FunctionTypes.h"],
      options := #[s!"-Drumoca.fmi3.root={root}"] }
  | kind :: source :: input :: grammar :: galecGrammar :: names => do
    let name ← match names with
      | [] => pure source
      | [name] => pure name
      | _ => throw (IO.userError "expected one optional SOURCE_NAME")
    let directory : System.FilePath := input
    let (entry, option, files) ← match kind with
      | "algorithm" => pure ("CheckEFMIAlgorithm.lean", "algorithm", #[directory])
      | "efmi-archive" => pure ("CheckEFMIArchive.lean", "root", #[directory])
      | "efmi-directory" => pure ("CheckEFMIManifests.lean", "root", #[
          directory / "AlgorithmCode/model.alg", directory / "ProductionCode/production.c",
          directory / "AlgorithmCode/manifest.xml", directory / "ProductionCode/manifest.xml",
          directory / "__content.xml"])
      | _ => throw (IO.userError s!"unknown artifact kind: {kind}")
    return {
      kind, sourceName := name, entry := tools / entry,
      inputs := #[source, grammar, galecGrammar].map System.FilePath.mk ++ files,
      options := #[s!"-Drumoca.efmi.source={source}", s!"-Drumoca.efmi.{option}={input}",
        s!"-Drumoca.efmi.grammar={grammar}", s!"-Drumoca.efmi.galecGrammar={galecGrammar}"] }
  | _ => throw (IO.userError "expected c SOURCE C GRAMMAR; fmi3 ROOT [SOURCE_NAME]; or {algorithm|efmi-archive|efmi-directory} SOURCE INPUT GRAMMAR GALEC [SOURCE_NAME]")

/-- Kernel-check actual artifact bytes, reusing native Lake proof products. -/
script «verify-artifact» args do
  let checkOnly := args.head? == some "--check-only"
  let request ← certificateRequest (if checkOnly then args.drop 1 else args)
  if request.sourceName.isEmpty then throw (IO.userError "source identity must not be empty")
  let report ← runBuild (certificateJob request) {verbosity := .quiet, noBuild := checkOnly}
  IO.print (← IO.FS.readFile report)
  return 0

private def buildDir : ScriptM Unit := do
  IO.FS.createDirAll ((← getRootPackage).dir / "build")

private def lalrgen := "packages/parser/.lake/build/bin/lalrgen"
private def compiler := "packages/compiler/.lake/build/bin/rumoca"
private def modelicaGrammar := "packages/modelica-parser/grammar/Modelica.ebnf"
private def galecGrammar := "packages/galec-parser/grammar/GALEC.ebnf"
private def generatedGrammar := "packages/modelica-parser/ModelicaParser/Generated.lean"
private def generatedGALEC := "packages/galec-parser/GALECParser/Generated.lean"

/-- Regenerate the checked-in Modelica and GALEC candidate tables. -/
script generate args do
  noArgs args
  buildTargets ["parser/lalrgen"]
  command lalrgen #["--namespace", "Rumoca.Generated", modelicaGrammar, generatedGrammar]
  command lalrgen #["--namespace", "Rumoca.GALEC.Generated", galecGrammar, generatedGALEC]
  return 0

private def checkGenerated : ScriptM Unit := do
  IO.println "Checking generated grammars"
  buildTargets ["parser/lalrgen"]
  buildDir
  command lalrgen #["--namespace", "Rumoca.Generated", modelicaGrammar, "build/ModelicaGenerated.check.lean"]
  command "cmp" #["build/ModelicaGenerated.check.lean", generatedGrammar]
  command lalrgen #["--namespace", "Rumoca.GALEC.Generated", galecGrammar, "build/GALECGenerated.check.lean"]
  command "cmp" #["build/GALECGenerated.check.lean", generatedGALEC]

private def lalrTest : ScriptM Unit := do
  IO.println "Checking LALR artifacts and execution"
  buildTargets ["parser/lalrgen", "modelica_parser/lalr-tests", "check-modelica-parser"]
  command "bash" #["tests/lalr.sh"]

private def frontendTest : ScriptM Unit := do
  buildTargets ["rumoca_compiler/rumoca", "rumoca_lsp/rumoca-lsp", "check-modelica-parser", "check-lsp"]
  command "python3" #["tests/lsp.py"]
  command "python3" #["tests/parallel-parser.py"]

private def leanTest : ScriptM Unit := do
  checkGenerated
  buildTargets ["all", "check-packages", "audit"]
  command "packages/compiler/.lake/build/bin/tests"
  command "bash" #["tests/integration.sh"]
  lalrTest
  frontendTest

private def verifyC : ScriptM Unit := do
  IO.println "Checking actual source/C contracts and rejection controls"
  buildTargets ["rumoca_compiler"]
  command "bash" #["scripts/verify-artifact.sh"]
  command "bash" #["tests/verification-negative.sh"]

private def tensorCTest : ScriptM Unit := do
  IO.println "Checking development tensor C helper artifacts"
  buildTargets ["check-c", "rumoca_c/RumocaC.TensorArtifactCheck",
    "rumoca_c/TensorCChecks.ArtifactCheck"]
  command "bash" #["tests/tensor-c.sh"]

private def fmiTest : ScriptM Unit := do
  IO.println "Checking FMI 3 archives, importers and native interfaces"
  buildTargets ["rumoca_compiler", "rumoca_fmu_runner", "rumoca_fmi3/RumocaFMI3"]
  command "bash" #["tests/fmi3.sh"]

private def efmiAlgorithmTest : ScriptM Unit := do
  IO.println "Checking actual GALEC artifacts"
  buildTargets ["parser/lalrgen", "rumoca_compiler/rumoca", "rumoca_compiler/Rumoca.EFMIArtifactCheck"]
  command "bash" #["tests/efmi-algorithm.sh"]

private def efmiProductionTest : ScriptM Unit := do
  IO.println "Checking actual eFMI Production C and manifest contracts"
  buildTargets ["rumoca_compiler/rumoca", "rumoca_compiler/Rumoca.EFMIManifestArtifactCheck"]
  command "bash" #["tests/efmi-production.sh"]

-- These boundary checks intentionally run on each invocation. They read actual
-- external files; only their Lean prerequisites use the module build cache.
script «check-generated» args do noArgs args; checkGenerated; return 0
script «lalr-test» args do noArgs args; lalrTest; return 0
script «frontend-test» args do noArgs args; frontendTest; return 0

/-- Opt-in native measurements; independent of the semantic verification gate. -/
script «benchmark-frontend» args do
  buildTargets ["rumoca_compiler/rumoca", "modelica_parser/frontend-bench"]
  command "python3" (#["scripts/benchmark-frontend.py", "--compiler", compiler,
    "--stage-compiler", "packages/modelica-parser/.lake/build/bin/frontend-bench"] ++ args.toArray)
  return 0

/-- Optional external numerical comparison, separate from the proof gate. -/
script «compare-omc» args do
  buildTargets ["rumoca_compiler/rumoca", "rumoca_fmu_runner/fmu-runner"]
  command "python3" (#["tests/compare-omc.py", "--compiler", compiler,
    "--runner", "packages/fmu-runner/.lake/build/bin/fmu-runner"] ++ args.toArray)
  return 0

script «verify-c» args do noArgs args; verifyC; return 0
script «tensor-c-test» args do noArgs args; tensorCTest; return 0
script «fmi-test» args do noArgs args; fmiTest; return 0
script «efmi-algorithm-test» args do noArgs args; efmiAlgorithmTest; return 0
script «efmi-production-test» args do noArgs args; efmiProductionTest; return 0

/-- Complete verification gate: proofs, actual artifacts, rejection and native execution. -/
@[test_driver]
script test args do
  noArgs args
  leanTest
  verifyC
  tensorCTest
  fmiTest
  efmiAlgorithmTest
  efmiProductionTest
  return 0

/-- Build and validate the combined Model Exchange / Co-Simulation FMU. -/
script fmu args do
  noArgs args
  buildTargets ["all"]
  command compiler #["examples/Integrator.mo", "-o", "build/Integrator.fmu"]
  return 0

/-- Compile and execute three unit steps of the tiny example. -/
script demo args do
  noArgs args
  buildTargets ["all"]
  buildDir
  command compiler #["examples/Integrator.mo", "-o", "build/model.c"]
  command "cc" #["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-pedantic",
    "-fno-fast-math", "-ffp-contract=off", "build/model.c", "examples/driver.c", "-lm", "-o", "build/simulate"]
  command "build/simulate" #["3", "0.5"]
  return 0
