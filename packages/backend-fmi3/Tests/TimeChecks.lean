import RumocaFMI3.CInterface
import ProofAudit.Audit
import RumocaFMI3.TimeProofs
import Tests.UnitFixture

/-! Encoding and generated-body controls for ME time. These discriminate
numerical comparison from bit equality and preserve valid backtracking.
Rejected guards do not claim that the subsequent logging path is proved. -/
namespace Rumoca.FMI3.TimeChecks
private local instance : StaticLiterals := ⟨fun _ => none⟩
private local instance targetInterface : CInterface := cInterface
open CTree CMemory CBody
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def bits (n : Nat) : Value := .float64 (BitVec.ofNat 64 n)

theorem signed_zeros_equal :
    comparison .eq (bits 0) (bits 0x8000000000000000) = some (boolean true) := by decide +kernel

theorem negative_subnormal_less_than_zero :
    comparison .lt (bits 0x8000000000000001) (bits 0) = some (boolean true) := by decide +kernel

theorem adjacent_normal_order :
    comparison .lt (bits 0x3ff0000000000000) (bits 0x3ff0000000000001) = some (boolean true) := by
  decide +kernel

theorem infinity_order :
    comparison .lt (bits 0xfff0000000000000) (bits 0) = some (boolean true) ∧
    comparison .gt (bits 0x7ff0000000000000) (bits 0) = some (boolean true) ∧
    comparison .eq (bits 0x7ff0000000000000) (bits 0x7ff0000000000000) = some (boolean true) := by
  decide +kernel

theorem nan_unordered :
    [0x7ff8000000000000, 0x7ff0000000000001, 0xfff8000000000042].all (fun n =>
      comparison .eq (bits n) (bits n) == some (boolean false) &&
      comparison .ne (bits n) (bits n) == some (boolean true) &&
      comparison .le (bits n) (bits 0) == some (boolean false) &&
      comparison .gt (bits 0) (bits n) == some (boolean false)) = true := by
  decide +kernel

theorem mixed_zero_comparison :
    comparison .lt (bits 0x8000000000000001) (.integer 0) = some (boolean true) := by decide +kernel

/-- General integer-to-double conversion is still outside this fragment;
comparing exact integer units would silently give the wrong C result here. -/
theorem unsupported_integer_conversion_stuck :
    comparison .eq (bits 0x4340000000000000) (.integer (2 ^ 53 + 1)) = none := by decide +kernel

open UnitFixture (prepared)
def setter : List Stmt := Runtime.body prepared ⟨"fmi3Status", "fmi3SetTime", []⟩
def model : Address := ⟨1, [], 0⟩
def heap (stop : Bool) : Heap := fun p =>
  if p = model.member "kind" then some ⟨.int32, true, some (.integer 0)⟩
  else if p = model.member "mode" then some ⟨.int32, true, some (.integer 3)⟩
  else if p = model.member "time" then some ⟨.float64, true, some (.finite Binary64.one)⟩
  else if p = model.member "timeMin" then some ⟨.float64, true, some (.finite Binary64.half)⟩
  else if p = model.member "stopDefined" then some ⟨.boolean, true, some (boolean stop)⟩
  else if stop && p = model.member "stop" then some ⟨.float64, true, some (.finite Binary64.threeHalves)⟩
  else if p = StateProofs.stateAddress model then some ⟨.float64, true, some (.finite Binary64.negativeZero)⟩
  else none

noncomputable def observe (body : List Stmt) (stop : Bool) (time : Binary64.Value) : Option (Value × Option Value × Option Value) := do
  let .returned result ← run 6 (.running body
    (TimeProofs.parameters model (Binary64.toBits time).val) (heap stop)) | none
  return (result.value, load result.heap (model.member "time"),
    load result.heap (StateProofs.stateAddress model))

theorem backward_trial_time_allowed :
    observe setter true Binary64.half =
      some (.integer 0, some (.finite Binary64.half), some (.finite Binary64.negativeZero)) := by decide +kernel

theorem unused_stop_not_loaded :
    observe setter false Binary64.one =
      some (.integer 0, some (.finite Binary64.one), some (.finite Binary64.negativeZero)) := by decide +kernel

theorem stop_equality_allowed :
    observe setter true Binary64.threeHalves =
      some (.integer 0, some (.finite Binary64.threeHalves), some (.finite Binary64.negativeZero)) := by decide +kernel

noncomputable def guard (stop : Bool) (raw : Nat) : Option Value :=
  eval (TimeProofs.locals model (BitVec.ofNat 64 raw)) (heap stop) Runtime.invalidTime

theorem history_lower_bound_rejects : guard false 0 = some (boolean true) := by decide +kernel
theorem stop_upper_bound_rejects : guard true 0x4000000000000000 = some (boolean true) := by decide +kernel
theorem nonfinite_time_rejects :
    [0x7ff8000000000000, 0x7ff0000000000001, 0x7ff0000000000000, 0xfff0000000000000].all
      (fun n => guard false n == some (boolean true)) = true := by decide +kernel

def wrongValue : List Stmt := setter.map fun s => match s with
  | .assign target _ => .assign target (.nat 0)
  | s => s

theorem altered_time_write_detected :
    observe wrongValue true Binary64.half ≠ observe setter true Binary64.half := by decide +kernel

end Rumoca.FMI3.TimeChecks

#audit axioms Rumoca.FMI3.TimeChecks.signed_zeros_equal
#audit axioms Rumoca.FMI3.TimeChecks.negative_subnormal_less_than_zero
#audit axioms Rumoca.FMI3.TimeChecks.adjacent_normal_order
#audit axioms Rumoca.FMI3.TimeChecks.infinity_order
#audit axioms Rumoca.FMI3.TimeChecks.nan_unordered
#audit axioms Rumoca.FMI3.TimeChecks.mixed_zero_comparison
#audit axioms Rumoca.FMI3.TimeChecks.unsupported_integer_conversion_stuck
#audit axioms Rumoca.FMI3.TimeChecks.backward_trial_time_allowed
#audit axioms Rumoca.FMI3.TimeChecks.unused_stop_not_loaded
#audit axioms Rumoca.FMI3.TimeChecks.stop_equality_allowed
#audit axioms Rumoca.FMI3.TimeChecks.history_lower_bound_rejects
#audit axioms Rumoca.FMI3.TimeChecks.stop_upper_bound_rejects
#audit axioms Rumoca.FMI3.TimeChecks.nonfinite_time_rejects
#audit axioms Rumoca.FMI3.TimeChecks.altered_time_write_detected
