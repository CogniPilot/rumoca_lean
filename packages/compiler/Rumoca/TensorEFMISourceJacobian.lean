import Rumoca.EFMITensorArchiveProofs
import RumocaEFMI.TensorJacobianObservation

noncomputable section
namespace Rumoca.EFMI.JacobianObservation
open CMemory CMemory.TensorView Rumoca.Tensor CTensor
open CTensor.SquareJacobianObservation
open TensorNumericalLinkage

/-- The existing parsed Algorithm contract already pins the SAME artifact's
prepared IVP to the square plan; no extra source/index hypothesis is needed. -/
theorem prepared_index (a : TensorArtifact input)
    (contract : TensorProductionContract a algorithm c) :
    a.prepared.kernel = CTensor.ProgramFixture.IVPEntry.kernel ArrayProfile.stateShape := by
  obtain ⟨parsed, _, denotes⟩ := contract.algorithm_contract.parsed
  exact denotes.2.trans rfl

/-- Actual production bytes determine the exact seven numerical and three
method trees. This is a byte/table identity, not a method-execution theorem. -/
theorem actual_trees (a : TensorArtifact input)
    (contract : TensorProductionContract a algorithm c) :
    c = "#include <stddef.h>\n#include <stdint.h>\n" ++
      String.join (numericalFunctions.map CTree.Function.render) ++
      TensorProduction.header ++
      String.join (TensorProduction.functions.map CTree.Function.render) :=
  contract.bytes.symm.trans production_exact

/-- The mathematical target is the independently specified parsed source
`jacobian` built-in, not merely a diagonal formula attached to a C helper. -/
theorem source_builtin (m : ArrayProfile.Model) (resolved : m.Resolved)
    (body : m.body = .jacobian output derivative rhs assigned call)
    (values : String → Values shape) :
    call.Denotes (fun name i => Binary64.value (values name)[i])
      (mathematical (values m.header.state) (values m.header.input)) := by
  rw [mathematical_eq]
  exact m.jacobian_call_correct resolved body _

end Rumoca.EFMI.JacobianObservation
