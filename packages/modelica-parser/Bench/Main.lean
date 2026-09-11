import ModelicaParser.LocatedParser

/-! Optional native measurement entry point. It calls the existing frontend
stages without artifact backends or diagnostic rendering. No compiler logic
or alternative parser lives here; external measurements are not proof roots. -/

private def frontendStage (stage source : String) : Bool × Nat :=
  match stage with
  | "read" => (true, source.utf8ByteSize)
  | "lex" => match Rumoca.lex source with
      | .ok tokens => (true, tokens.length)
      | .error error => (false, error.offset)
  | "parse" => match Rumoca.parse source with
      | .ok parsed => (true, parsed.tokens.length + parsed.ast.name.length)
      | .error error => (false, error.offset)
  | _ => match Rumoca.parseLocated source with
      | .ok parsed => (true, parsed.locations.length + parsed.parsed.ast.name.length)
      | .error error => (false, error.span.start.offset.byteIdx)

def main (args : List String) : IO UInt32 := do
  let [stage, file] := args
    | IO.eprintln "usage: frontend-bench {read|lex|parse|located} FILE"; return 2
  unless ["read", "lex", "parse", "located"].contains stage do
    IO.eprintln "unknown frontend stage"
    return 2
  let source ← IO.FS.readFile file
  let start ← IO.monoNanosNow
  let (accepted, observation) := frontendStage stage source
  let stop ← IO.monoNanosNow
  IO.println s!"{stage}: accepted={accepted} observation={observation} elapsed_ns={stop - start}"
  -- Linux's post-exec high-water mark excludes the Python launcher's heap.
  let status ← IO.FS.readFile "/proc/self/status"
  for line in status.splitOn "\n" do
    if line.startsWith "VmHWM:" then IO.println line
  return if accepted then 0 else 1
