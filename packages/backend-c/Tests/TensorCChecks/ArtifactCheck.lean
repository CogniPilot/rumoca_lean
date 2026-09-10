import TensorCChecks.Fixture
import Lean

/-! Fixed file-to-proposition adapter for the single development program fixture.
Neither producer commands nor producer-supplied propositions are executed. -/
namespace Rumoca.CTensor.ProgramFixture.ArtifactCheck
open Lean Elab Command

elab "verify_tensor_program " path:str : command => do
  let source ← IO.FS.readFile path.getString
  if source != code then
    throwError "actual tensor program differs from the certified Solve emission"
  let literal := Lean.Syntax.mkStrLit source
  let theoremName := `Rumoca.CTensor.CheckedProgram.contract
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    set_option maxRecDepth 10000 in
    theorem $theoremId:ident : ProgramFixture.ArtifactContract $literal := by
      apply ProgramFixture.artifact_correct
      tensor_expand_program_fixture
      decide +kernel))
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor program file contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {dependencies.toList}"

end Rumoca.CTensor.ProgramFixture.ArtifactCheck
