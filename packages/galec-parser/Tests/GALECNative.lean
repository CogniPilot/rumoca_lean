import GALECParser.Parser

open _root_.Parser

open Rumoca

def main : IO Unit := do
  let source ← IO.FS.readFile "examples/UnitIntegrator.alg"
  let accepted : Array String := #[source,
    source.replace "\n" "\r\n\t",
    source.replace "UnitIntegrator" "AnotherBlock" |>.replace "samplePeriod" "period"]
  for text in accepted do
    match GALEC.Syntax.parse text with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"valid tiny GALEC profile rejected: {e}")
  let rejected : Array String := #[
    source.replace "end UnitIntegrator" "end Different",
    source.replace "self.x := 0.0" "self.missing := 0.0",
    source.replace "self.samplePeriod :=" "self.missing :=",
    source.replace "(self.x +" "(self.samplePeriod +",
    source.replace "constant Real samplePeriod" "constant Real x",
    source.replace "0.0" "1.0",
    source.replace "1.0" "2.0",
    source.replace "+" "-",
    source.replace ":=" ":",
    source.replace "end Recalibrate;" "end Startup;",
    source ++ "garbage"]
  for text in rejected do
    if (GALEC.Syntax.parse text).isOk then
      throw (IO.userError "malformed or out-of-profile GALEC accepted")
  IO.println s!"GALEC: {accepted.size} accepted and {rejected.size} rejected source cases passed"
