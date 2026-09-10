import RumocaFMI3.CInterface
import ProofAudit.Audit
import RumocaFMI3.StateProofs

/-! Negative controls for the generated-body semantics. These witnesses expose
wrong values, writes into another instance, missing storage and unsupported
calls. They are not an alternative definition of FMI compliance. -/
namespace Rumoca.FMI3.MemoryChecks
private local instance : StaticLiterals := ⟨fun _ => none⟩
private local instance targetInterface : CInterface := cInterface
open CTree CMemory CBody StateProofs
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def source : AST.Model := ⟨"M", "x", "x", "M"⟩
def prepared : Solve.FMI3Model source :=
  (Solve.lower (DAE.lower (Flat.lower source ⟨rfl, rfl⟩))).prepareFMI3
def getter : List Stmt := Runtime.body prepared ⟨"fmi3Status", "fmi3GetContinuousStates", []⟩

def model : Address := ⟨1, [], 0⟩
def output : Address := ⟨2, [], 0⟩
def other : Address := ⟨3, [], 0⟩
def heap : Heap := fun p =>
  if p = model.member "kind" then some ⟨.int32, true, some (.integer 0)⟩
  else if p = model.member "mode" then some ⟨.int32, true, some (.integer 3)⟩
  else if p = stateAddress model then some ⟨.float64, true, some (.finite Binary64.negativeZero)⟩
  else if p = stateAddress other then some ⟨.float64, true, some (.finite Binary64.one)⟩
  else if p = output then some ⟨.float64, true, none⟩
  else none

def observe (code : List Stmt) : Option (Value × Option Value × Option Value) := do
  let .returned result ← run 6 (.running code (parameters model output) heap) | none
  return (result.value, load result.heap output, load result.heap (stateAddress other))

theorem preserves_signed_zero :
    observe getter = some (.integer 0, some (.finite Binary64.negativeZero), some (.finite Binary64.one)) := by
  decide +kernel

/-- Replacing the state copy by a constant produces a different encoding. -/
def wrongValue : List Stmt := getter.map fun s => match s with
  | .assign target _ => .assign target (.nat 1)
  | s => s

theorem wrong_value_observed :
    observe wrongValue = some (.integer 0, some (.finite Binary64.one), some (.finite Binary64.one)) := by
  decide +kernel

theorem wrong_value_not_equivalent : observe wrongValue ≠ observe getter := by decide +kernel

/-- Redirecting the output pointer into another instance changes that instance.
The body contract describes the write, while the separate-block precondition
is essential to a model-isolation claim. -/
theorem alias_changes_other_instance :
    (do
      let .returned result ← run 6 (.running getter (parameters model (stateAddress other)) heap) | none
      load result.heap (stateAddress other)) = some (.finite Binary64.negativeZero) := by
  decide +kernel

theorem missing_storage_stuck :
    (run 6 (.running getter (parameters model ⟨99, [], 0⟩) heap)).isNone = true := by decide +kernel

theorem unsupported_call_stuck :
    next (.running [.eval (.call (.id "unimplemented") [])] (parameters model output) heap) = none := rfl

#audit axioms preserves_signed_zero
#audit axioms wrong_value_observed
#audit axioms wrong_value_not_equivalent
#audit axioms alias_changes_other_instance
#audit axioms missing_storage_stuck
#audit axioms unsupported_call_stuck
end Rumoca.FMI3.MemoryChecks
