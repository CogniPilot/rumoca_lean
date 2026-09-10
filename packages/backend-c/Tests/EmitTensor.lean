import RumocaC.TensorCode
import RumocaC.TensorFillCode

/-- Development artifact fixture. No array source is admitted by this tool. -/
def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: EmitTensor.lean OUTPUT_DIRECTORY")
  IO.FS.createDirAll directory
  let root : System.FilePath := directory
  IO.FS.writeFile (root / "add.c") (Rumoca.CTensor.function .add).render
  IO.FS.writeFile (root / "mul.c") (Rumoca.CTensor.function .mul).render
  IO.FS.writeFile (root / "fill.c") Rumoca.CTensor.Fill.function.render
