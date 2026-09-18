import TensorCChecks.ConstantEntry

/-- Development artifact fixture. No constant-rate source is admitted by this
tool; it writes the certified numerical C bytes for the fixture rates. -/
def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: EmitConstant.lean OUTPUT_DIRECTORY")
  IO.FS.createDirAll directory
  let root : System.FilePath := directory
  IO.FS.writeFile (root / "constant.c") Rumoca.CConstant.Fixture.source
