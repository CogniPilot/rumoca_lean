import RumocaC.TensorCode
import RumocaC.TensorFillCode
import RumocaC.TensorDiagonalCode
import RumocaC.TensorFiniteScanCode
import RumocaC.TensorProductPreflightCode
import RumocaC.TensorSquareDiagonal
import TensorCChecks.IVPEntry

/-- Development artifact fixture. No array source is admitted by this tool. -/
def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: EmitTensor.lean OUTPUT_DIRECTORY")
  IO.FS.createDirAll directory
  let root : System.FilePath := directory
  IO.FS.writeFile (root / "add.c") (Rumoca.CTensor.function .add).render
  IO.FS.writeFile (root / "mul.c") (Rumoca.CTensor.function .mul).render
  IO.FS.writeFile (root / "sub.c") (Rumoca.CTensor.function .sub).render
  IO.FS.writeFile (root / "div.c") (Rumoca.CTensor.function .div).render
  IO.FS.writeFile (root / "fill.c") Rumoca.CTensor.Fill.function.render
  IO.FS.writeFile (root / "diagonal.c") Rumoca.CTensor.Diagonal.function.render
  IO.FS.writeFile (root / "finite.c") Rumoca.CTensor.FiniteScan.function.render
  IO.FS.writeFile (root / "product_finite.c") Rumoca.CTensor.ProductPreflight.function.render
  IO.FS.writeFile (root / "jacobian-diag.c") Rumoca.CTensor.SquareDiagonal.function.render
  let sources := Rumoca.CTensor.ProgramFixture.IVPEntry.sources
  IO.FS.writeFile (root / "initial.c") sources.initial
  IO.FS.writeFile (root / "derivative.c") sources.derivative
  if let some diagonal := sources.diagonal then
    IO.FS.writeFile (root / "jacobian.c") diagonal
