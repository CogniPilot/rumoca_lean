import Cli
import ModelicaParser.Parallel
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Position
import Rumoca.Diagnostics

open _root_.Parser

/-! File I/O and presentation for independent parallel frontend work. The
parser package owns the pure scheduler and its sequential-equivalence theorem.
No IR lowering, FMU build, or kernel subprocess runs for this command. -/
namespace Rumoca.CLI
open Lean

/-- Structured output is always produced. Terminal context is evaluated only
when requested; an empty message still records failure in JSON mode. -/
def analyze (terminal : Bool) (item : String × Except String String) : Json × Option String :=
  let (name, read) := item
  let failure (diagnostic : Json) (message : Unit → String) :=
    (Json.mkObj [("path", toJson name), ("ok", toJson false),
      ("diagnostics", toJson #[diagnostic])], some (if terminal then message () else ""))
  match read with
  | .error e => failure (Json.mkObj [("phase", "io"), ("message", toJson e)]) (fun _ => s!"{name}: {e}")
  | .ok source =>
    let error (e : Parser.Source.Diagnostic source) :=
      failure (Diagnostics.toJson e) (fun _ => Diagnostics.render name e)
    let result := Parallel.parseOne ⟨name, source⟩
    match result.parsed with
    | .error e => error e
    | .ok p => match p.resolve with
      | .error e => error e
      | .ok _ => (Json.mkObj [("path", toJson name), ("ok", toJson true),
          ("model", toJson p.parsed.ast.name), ("diagnostics", toJson (#[] : Array Json))], none)

private def runParseFiles (p : Cli.Parsed) : IO UInt32 := do
  let jobs := (p.flag? "jobs").map (·.as! Nat) |>.getD 4
  if jobs == 0 then throw (IO.userError "--jobs must be positive")
  let files := (p.positionalArg! "file" |>.as! String) :: (p.variableArgsAs! String).toList
  let mut snapshots : List (String × Except String String) := []
  for file in files do
    let read ← try pure (.ok (← IO.FS.readFile file)) catch e => pure (.error (toString e))
    snapshots := (file, read) :: snapshots
  let results := Parser.Parallel.map jobs (analyze (!p.hasFlag "json")) snapshots.reverse
  if p.hasFlag "json" then
    IO.println (toJson (results.map (·.1))).compress
  else
    for (result, error) in results do
      match error with
      | some message => IO.eprintln message
      | none => IO.println s!"{(result.getObjValAs? String "path").toOption.getD ""}: parsed"
  return if results.any (·.2.isSome) then 1 else 0

def parseFiles : Cli.Cmd := `[Cli|
  "parse" VIA runParseFiles;
  "Parse independent tiny Modelica files in parallel, with source ranges and deterministic result order."
  FLAGS:
    j, jobs : Nat; "Maximum parser parallelism (default: 4; must be positive)."
    json; "Emit one JSON array, including file paths and byte ranges."
  ARGS:
    file : String; "First Modelica source file."
    ...files : String; "Additional Modelica source files."
]

end Rumoca.CLI
