import RumocaC.TensorCallContract
import RumocaC.TensorFillContract
import RumocaC.TensorDiagonalContract
import RumocaC.TensorFiniteScanContract
import Lean

/-! Trusted file-to-proposition adapter for the development tensor C
helpers. The caller supplies only a path and operator; the adapter itself
reads the complete file and constructs the fixed semantic contract. It never
executes producer-supplied Lean commands or trusts a producer's proposition. -/
namespace Rumoca.CTensor.ArtifactCheck
open Lean Elab Command

elab "verify_tensor_helper " path:str " as " operation:ident : command => do
  let expected ← match operation.getId with
    | `add => pure (function .add).render
    | `mul => pure (function .mul).render
    | `sub => pure (function .sub).render
    | `div => pure (function .div).render
    | `fill => pure Fill.function.render
    | `diagonal => pure Diagonal.function.render
    | `finite => pure FiniteScan.function.render
    | _ => throwError "expected tensor helper add, mul, sub, div, fill, diagonal or finite"
  let source ← IO.FS.readFile path.getString
  -- Early rejection is only a convenience. Kernel-checked literal equality
  -- below is the sole authorization for applying the artifact theorem.
  if source != expected then
    throwError "actual tensor C file differs from the certified helper"
  let literal := Syntax.mkStrLit source
  let statement ← match operation.getId with
    | `add => `(term| CallArtifactContract $literal Tensor.BinaryOp.add)
    | `mul => `(term| CallArtifactContract $literal Tensor.BinaryOp.mul)
    | `sub => `(term| CallArtifactContract $literal Tensor.BinaryOp.sub)
    | `div => `(term| CallArtifactContract $literal Tensor.BinaryOp.div)
    | `diagonal => `(term| Diagonal.ArtifactContract $literal)
    | `finite => `(term| FiniteScan.ArtifactContract $literal)
    | _ => `(term| Fill.ArtifactContract $literal)
  let proof ← match operation.getId with
    | `fill => `(tactic| (apply Fill.artifact_correct; tensor_expand_fill_printer; decide +kernel))
    | `diagonal => `(tactic| (apply Diagonal.artifact_correct; tensor_expand_diagonal_printer; decide +kernel))
    | `finite => `(tactic| (apply FiniteScan.artifact_correct; tensor_expand_finite_scan_printer; decide +kernel))
    | _ => `(tactic| (apply call_artifact_correct; tensor_expand_printer; decide +kernel))
  let theoremName := `Rumoca.CTensor.CheckedFile.contract
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    set_option maxRecDepth 10000 in
    theorem $theoremId:ident : $statement := by $proof:tactic))
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor C file contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {dependencies.toList}"

end Rumoca.CTensor.ArtifactCheck
