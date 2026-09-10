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

private def buildDir : ScriptM Unit := do
  IO.FS.createDirAll ((← getRootPackage).dir / "build")

private def ebnfgen := "packages/parser/.lake/build/bin/ebnfgen"
private def lalrgen := "packages/parser/.lake/build/bin/lalrgen"
private def compiler := "packages/compiler/.lake/build/bin/rumoca"
private def modelicaGrammar := "packages/modelica-parser/grammar/Modelica.ebnf"
private def galecGrammar := "packages/galec-parser/grammar/GALEC.ebnf"
private def generatedGrammar := "packages/modelica-parser/ModelicaParser/Generated.lean"
private def generatedRuntime := "packages/modelica-parser/ModelicaParser/GeneratedRuntime.lean"
private def generatedGALEC := "packages/galec-parser/GALECParser/Generated.lean"

/-- Regenerate the checked-in Modelica and GALEC candidate tables. -/
script generate args do
  noArgs args
  buildTargets ["parser/ebnfgen", "parser/lalrgen"]
  command ebnfgen #["--namespace", "Rumoca.Generated", modelicaGrammar, generatedGrammar]
  command ebnfgen #["--namespace", "Rumoca.RuntimeGenerated", "--runtime", modelicaGrammar, generatedRuntime]
  command lalrgen #["--namespace", "Rumoca.GALEC.Generated", galecGrammar, generatedGALEC]
  return 0

private def checkGenerated : ScriptM Unit := do
  IO.println "Checking generated grammars"
  buildTargets ["parser/ebnfgen", "parser/lalrgen"]
  command ebnfgen #["--namespace", "Rumoca.Generated", "--check", modelicaGrammar, generatedGrammar]
  command ebnfgen #["--namespace", "Rumoca.RuntimeGenerated", "--check-runtime", modelicaGrammar, generatedRuntime]
  buildDir
  command lalrgen #["--namespace", "Rumoca.GALEC.Generated", galecGrammar, "build/GALECGenerated.check.lean"]
  command "cmp" #["build/GALECGenerated.check.lean", generatedGALEC]

private def lalrTest : ScriptM Unit := do
  IO.println "Checking LALR artifacts and execution"
  buildTargets ["parser/lalrgen", "modelica_parser/lalr-tests"]
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
