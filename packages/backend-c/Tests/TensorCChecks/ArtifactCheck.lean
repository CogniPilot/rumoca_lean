import TensorCChecks.IVPEntry
import Lean

/-! Fixed actual-file adapter for the development IVP. Producer strings enter
only as quoted literals in the complete required proposition. -/
namespace Rumoca.CTensor.ProgramFixture.ArtifactCheck
open Lean Elab Command

elab "verify_tensor_ivp " path:str : command => do
  let root : System.FilePath := path.getString
  let initial ← IO.FS.readFile (root / "initial.c")
  let derivative ← IO.FS.readFile (root / "derivative.c")
  let diagonal ← IO.FS.readFile (root / "jacobian.c")
  let actual : Lowering.PointwiseSources := ⟨initial, derivative, some diagonal⟩
  if actual != IVPEntry.sources then
    throwError "actual tensor IVP differs from the certified Solve emission"
  let initialLiteral := Lean.Syntax.mkStrLit initial
  let derivativeLiteral := Lean.Syntax.mkStrLit derivative
  let diagonalLiteral := Lean.Syntax.mkStrLit diagonal
  let theoremName := `Rumoca.CTensor.CheckedIVP.contract
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    set_option maxRecDepth 10000 in
    theorem $theoremId:ident : IVPEntry.ArtifactContract
        ⟨$initialLiteral, $derivativeLiteral, some $diagonalLiteral⟩ := by
      apply IVPEntry.artifact_correct
      tensor_expand_ivp_fixture
      decide +kernel))
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor IVP file contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {dependencies.toList}"

end Rumoca.CTensor.ProgramFixture.ArtifactCheck
