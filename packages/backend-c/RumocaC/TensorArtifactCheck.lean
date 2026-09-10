import RumocaC.TensorContract
import Lean

/-! Trusted file-to-proposition adapter for the two development tensor C
helpers. The caller supplies only a path and operator; the adapter itself
reads the complete file and constructs the fixed semantic contract. It never
executes producer-supplied Lean commands or trusts a producer's proposition. -/
namespace Rumoca.CTensor.ArtifactCheck
open Lean Elab Command

elab "verify_tensor_helper " path:str " as " operation:ident : command => do
  let op ← match operation.getId with
    | `add => pure Tensor.BinaryOp.add
    | `mul => pure Tensor.BinaryOp.mul
    | _ => throwError "expected tensor operator add or mul"
  let source ← IO.FS.readFile path.getString
  -- Early rejection is only a convenience. Kernel-checked literal equality
  -- below is the sole authorization for applying the artifact theorem.
  if source != (function op).render then
    throwError "actual tensor C file differs from the certified helper"
  let literal := Syntax.mkStrLit source
  let term ← match op with
    | .add => `(term| Tensor.BinaryOp.add)
    | .mul => `(term| Tensor.BinaryOp.mul)
  let theoremName := `Rumoca.CTensor.CheckedFile.contract
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    set_option maxRecDepth 10000 in
    theorem $theoremId:ident : ArtifactContract $literal $term := by
      apply artifact_correct
      tensor_expand_printer
      decide +kernel))
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor C file contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {dependencies.toList}"

end Rumoca.CTensor.ArtifactCheck
