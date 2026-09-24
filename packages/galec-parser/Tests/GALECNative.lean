import GALECParser.Parser

open _root_.Parser

open Rumoca

/-! Native boundary for the GALEC source entrypoint on actual file text. Only
syntax is decided here; declaration, name, shape and method admission are
static semantics checked after parsing. -/
def main : IO Unit := do
  let source ← IO.FS.readFile "examples/UnitIntegrator.alg"
  let accepted : Array String := #[source,
    source.replace "\n" "\r\n\t",
    source.replace "UnitIntegrator" "AnotherBlock" |>.replace "samplePeriod" "period",
    source.replace "self.x := (self.x + 1.0);"
      "for k in 1:1:size(self.x, 1) loop\n self.x[k] := self.x[k] * 2;\n end for;"]
  for text in accepted do
    match GALEC.Syntax.parse text with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"valid GALEC syntax rejected: {e}")
  let rejected : Array String := #[
    source.replace ":=" ":",
    source.replace "+" "-",
    source.replace "+" ".*",
    source.replace "constant Real" "parameter Real",
    source.replace "output Real x" "output constant Real x",
    source.replace "Real x" "Real[1] x",
    source.replace "    algorithm\n    end Recalibrate;" "    end Recalibrate;",
    source.replace "end UnitIntegrator;" "end UnitIntegrator",
    source ++ "garbage"]
  for text in rejected do
    if (GALEC.Syntax.parse text).isOk then
      throw (IO.userError "malformed GALEC syntax accepted")
  IO.println s!"GALEC: {accepted.size} accepted and {rejected.size} rejected source cases passed"
