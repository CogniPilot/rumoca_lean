import Cli
import Rumoca.EFMIExport
import Rumoca.EFMICheck
import Rumoca.ParseFiles

open _root_.Parser

namespace Rumoca.CLI
open Cli

private def runCompiler (p : Cli.Parsed) : IO UInt32 := do
  let input := p.positionalArg! "model" |>.as! String
  let source ← IO.FS.readFile input
  match compile source with
  | .error error =>
    IO.eprintln (Diagnostics.render input error)
    return 1
  | .ok artifact =>
    match p.flag? "output" with
    | none => IO.print artifact.cSource
    | some flag =>
      let path := flag.as! String
      if path.endsWith ".fmu" then FMU.build source artifact path
      else if path.endsWith ".alg" then EFMIExport.writeAlgorithm source artifact path
      else if path.endsWith ".efmu" then EFMIExport.writeArchive source artifact path
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
