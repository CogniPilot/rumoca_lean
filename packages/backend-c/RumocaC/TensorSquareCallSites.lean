import RumocaC.TensorSquareTable
import RumocaC.LoopCallSites

/-! Checked direct-call inventory of the exact square numerical tree table. -/
noncomputable section
namespace Rumoca.TensorKernel
open CTree CMemory CCalls CCallSites CCallSites.LoopCalls

def helperNames : List String :=
  ["rumoca_tensor_fill", "rumoca_tensor_add", "rumoca_tensor_mul", "rumoca_tensor_diagonal"]

def helperCheck (operand : Indirect.Operand) : Bool :=
  match operand.callee with
  | .id name => helperNames.contains name
  | _ => false

theorem helperCheck_sound (operand : Indirect.Operand) (checked : helperCheck operand = true) :
    DirectNames (fun name => name ∈ helperNames) operand := by
  intro name callee
  simpa [helperCheck, callee] using checked

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem functions_checked : functions.all (checkFunction helperCheck) = true := by
  decide +kernel

theorem functions_admitted :
    DefinitionsAdmit (DirectNames (fun name => name ∈ helperNames)) definitions := by
  intro name fn found stmt member
  have listed := (TreeTable.lookup_some functions name fn found).1
  have checked : checkFunction helperCheck fn = true :=
    (List.all_eq_true.mp functions_checked) fn listed
  have admitted := (checkFunction_correct helperCheck fn).mp checked stmt member
  exact admits_mono helperCheck_sound stmt admitted

end Rumoca.TensorKernel
