import Std

/-! A small, independent Lean CLI for FMPy. The importer and ME integrator are
reused host tools, outside Rumoca's compiler proof. No compiler dependency. -/
namespace FMURunner

def usage : String :=
  "usage: fmu-runner info|validate MODEL.fmu\n" ++
  "       fmu-runner simulate MODEL.fmu [--mode cs|me] [--start-time T]\n" ++
  "         [--stop T] [--step H] [--variable NAME] [--start NAME VALUE]\n" ++
  "         [--csv PATH] [--timeout SECONDS]\n" ++
  "Defaults: cs, start 0, stop 3, step 1; ME uses FMPy's Euler solver.\n" ++
  "Repeat --variable/--start as needed. With no --variable, record FMI outputs."

private def simulation (file : String) (options : List String) : Except String (Array String) := do
  let mut mode := "CoSimulation"
  let mut start := "0"
  let mut stop := "3"
  let mut step := "1"
  let mut rest := options
  let mut variables : Array String := #[]
  let mut starts : Array String := #[]
  let mut extra : Array String := #[]
  for _ in [:options.length] do
    match rest with
    | [] => break
    | "--mode" :: value :: tail =>
      mode ← match value with
        | "cs" => pure "CoSimulation" | "me" => pure "ModelExchange"
        | _ => throw "--mode must be cs or me"
      rest := tail
    | "--start-time" :: value :: tail => start := value; rest := tail
    | "--stop" :: value :: tail => stop := value; rest := tail
    | "--step" :: value :: tail => step := value; rest := tail
    | "--variable" :: value :: tail => variables := variables.push value; rest := tail
    | "--start" :: name :: value :: tail => starts := starts ++ #[name, value]; rest := tail
    | "--csv" :: value :: tail => extra := extra ++ #["--output-file", value]; rest := tail
    | "--timeout" :: value :: tail => extra := extra ++ #["--timeout", value]; rest := tail
    | option :: _ => throw s!"Unknown or incomplete option: {option}"
  let base := #["simulate", file, "--validate", "--interface-type", mode,
    "--solver", "Euler", "--dont-record-events", "--start-time", start,
    "--stop-time", stop, "--step-size", step, "--output-interval", step]
  return base ++ extra ++
    (if variables.isEmpty then #[] else #["--output-variables"] ++ variables) ++
    (if starts.isEmpty then #[] else #["--start-values"] ++ starts)

def arguments : List String → Except String (Array String)
  | ["info", file] => .ok #["info", file]
  | ["validate", file] => .ok #["validate", file]
  | "simulate" :: file :: options => simulation file options
  | _ => .error usage

def run (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] then IO.println usage; return 0
  match arguments args with
  | .error message => IO.eprintln message; return 2
  | .ok args =>
    try
      let child ← IO.Process.spawn { cmd := "fmpy", args }
      return ← child.wait
    catch e =>
      IO.eprintln s!"Cannot run FMPy: {e}\nEnter nix develop, or install FMPy on PATH."
      return 1

end FMURunner
