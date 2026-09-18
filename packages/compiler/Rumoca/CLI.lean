import Cli
import Rumoca.EFMIExport
import Rumoca.EFMICheck
import Rumoca.ParseFiles
import Rumoca.InitializationDiagnostics
import Rumoca.TensorFMU

open _root_.Parser

namespace Rumoca.CLI
open Cli

/-- Publish an admitted array/tensor-profile source. The array profile is
admitted for FMI 3 FMU output, whose publication gate is the fixed `tensor-fmi3`
source-build certificate that `TensorFMU.build` runs, and for tensor eFMI
Algorithm Code (`.alg`) output, whose publication gate is the fixed
`tensor-algorithm` certificate. Tensor C emission on stdout is not built and is
rejected with a diagnostic. -/
private def runTensorCompiler {input : Source.InputRef} (name : String)
    (tensor : TensorArtifact input) (output : Option String) : IO UInt32 := do
  match output with
  | some path =>
    if path.endsWith ".fmu" then
      TensorFMU.build tensor path
      return 0
    else if path.endsWith ".alg" then
      EFMIExport.writeTensorAlgorithm tensor path
      return 0
    else if path.endsWith ".efmu" then
      IO.eprintln s!"{name}: tensor eFMU archive export is not built; the array/tensor profile is admitted for FMI 3 FMU (-o out.fmu) and tensor eFMI Algorithm Code (-o out.alg) output"
      return 1
    else
      IO.eprintln s!"{name}: the array/tensor profile is admitted for FMI 3 FMU (-o out.fmu), tensor eFMI Algorithm Code (-o out.alg) and tensor eFMU (-o out.efmu) output; tensor C emission is not built"
      return 1
  | none =>
    IO.eprintln s!"{name}: the array/tensor profile is admitted for FMI 3 FMU (-o out.fmu), tensor eFMI Algorithm Code (-o out.alg) and tensor eFMU (-o out.efmu) output; tensor C emission is not built"
    return 1

private def runCompiler (p : Cli.Parsed) : IO UInt32 := do
  let input := p.positionalArg! "model" |>.as! String
  let source ← IO.FS.readFile input
  let inputRef : Source.InputRef := .single input source
  let output := (p.flag? "output").map (·.as! String)
  match compile inputRef with
  | .error error =>
    -- The unit profile rejects the source. Admit the array/tensor profile if the
    -- source is the array-profile shape the fixed tensor certificate certifies;
    -- otherwise report the unit diagnostic and neither publish nor replace.
    match compileTensor inputRef with
    | .ok tensor => runTensorCompiler input tensor output
    | .error _ =>
      IO.eprintln (Diagnostics.render input error)
      return 1
  | .ok artifact =>
    for notice in artifact.initializationDiagnostics do
      IO.eprintln (Diagnostics.renderWarning input notice)
    match output with
    | none => IO.print artifact.cSource
    | some path =>
      if path.endsWith ".fmu" then FMU.build artifact path
      else if path.endsWith ".alg" then EFMIExport.writeAlgorithm artifact path
      else if path.endsWith ".efmu" then EFMIExport.writeArchive artifact path
      else IO.FS.writeFile path artifact.cSource
    return 0

private def runCheck (product : EFMICheck.Product) (p : Cli.Parsed) : IO UInt32 := do
  let source := p.flag! "source"
  let input := p.positionalArg! "input" |>.as! String
  let pathFlag (name : String) : Option System.FilePath :=
    (p.flag? name).map fun flag => flag.as! String
  IO.print (← EFMICheck.run product input (source.as! String)
    (pathFlag "grammar") (pathFlag "galec-grammar"))
  return 0

private def runAlgorithm := runCheck .algorithm
private def runEFMI := runCheck .efmi

def verifyAlgorithm : Cmd := `[Cli|
  "verify-algorithm" VIA runAlgorithm;
  "Kernel-check an actual GALEC file against its Modelica source."
  FLAGS:
    source : String; "Original Modelica file."
    grammar : String; "Override the workspace Modelica EBNF for verification."
    "galec-grammar" : String; "Override the workspace GALEC EBNF for verification."
  ARGS:
    input : String; "GALEC file."
  EXTENSIONS:
    require! #["source"]
]

def verifyEFMI : Cmd := `[Cli|
  "verify-efmi" VIA runEFMI;
  "Kernel-check the tiny eFMI code/manifest profile in a directory or complete archive."
  FLAGS:
    source : String; "Original Modelica file."
    grammar : String; "Override the workspace Modelica EBNF for verification."
    "galec-grammar" : String; "Override the workspace GALEC EBNF for verification."
  ARGS:
    input : String; "eFMU archive or root containing __content.xml, AlgorithmCode/ and ProductionCode/."
  EXTENSIONS:
    require! #["source"]
]

def command : Cmd := `[Cli|
  rumoca VIA runCompiler; ["0.1.0"]
  "Compile the verified tiny Modelica core or check its generated artifacts."
  FLAGS:
    o, output : String; "Output .c, .fmu, checked .alg or checked .efmu file; default: C on stdout."
  ARGS:
    model : String; "Modelica source file."
  SUBCOMMANDS:
    parseFiles;
    verifyAlgorithm;
    verifyEFMI
]

def main (args : List String) : IO UInt32 := do
  try command.validate args
  catch e => IO.eprintln (toString e); return (1 : UInt32)

end Rumoca.CLI
