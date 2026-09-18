import TensorCChecks.ConstantEntry
import Lean

/-! Fixed actual-file adapter for the development constant-rate numerical C. A
producer string enters only as a quoted literal in the complete required
proposition; the adapter reads the actual file and constructs the fixed
contract itself, executing no producer-supplied Lean. -/
namespace Rumoca.CConstant.ProgramFixture.ArtifactCheck
open Lean Elab Command

elab "verify_constant_kernel " path:str : command => do
  let actual ← IO.FS.readFile path.getString
  -- Early rejection is a convenience. The kernel-checked literal equality in the
  -- fixed theorem below is the sole authorization for applying the contract.
  if actual != Fixture.source then
    throwError "actual constant-rate C differs from the certified Solve emission"
  let literal := Lean.Syntax.mkStrLit actual
  let theoremName := `Rumoca.CConstant.CheckedFile.contract
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    set_option maxRecDepth 10000 in
    theorem $theoremId:ident : Contract Fixture.ivp $literal :=
      contract_correct Fixture.ivp $literal (by rw [Fixture.render_eq]; decide +kernel)))
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in constant-rate C file contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {dependencies.toList}"

end Rumoca.CConstant.ProgramFixture.ArtifactCheck
