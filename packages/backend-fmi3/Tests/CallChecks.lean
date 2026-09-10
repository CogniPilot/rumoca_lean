import RumocaFMI3.CInterface
import ProofAudit.Audit
import RumocaFMI3.DerivativeProofs

/-! Adversarial controls for interprocedural semantics. Changing a linked
helper or numerical body must change the observation; names alone do not
grant a function its intended behavior. All reductions are kernel checked. -/
noncomputable section
namespace Rumoca.FMI3.CallChecks
private local instance targetInterface : CInterface := cInterface
open CTree CMemory CCalls CallProofs
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def source : AST.Model := ⟨"M", "x", "x", "M"⟩
def prepared : Solve.FMI3Model source :=
  (Solve.lower (DAE.lower (Flat.lower source ⟨rfl, rfl⟩))).prepareFMI3
def heap : Heap := fun _ => none
def model : Address := ⟨1, [], 0⟩
def start : State := .calling "model_rhs" [.pointer (some model)] heap .done
def observe (program : Program) (steps : Nat) : Option Value := do
  let .halted result ← run program steps start | none
  return result.value

theorem linked_rhs_observed : observe (linked prepared) 8 = some (.finite Binary64.one) := by
  decide +kernel

def wrongHelper : Program := { linked prepared with
  definitions := fun name =>
    if name = "model_rhs" then some (.tree
      { Runtime.helpers[1] with body := [.ret (some (.nat 0))] })
    else (linked prepared).definitions name }

theorem changed_helper_observed : observe wrongHelper 4 = some (.finite Binary64.positiveZero) := by
  decide +kernel

theorem changed_helper_not_equivalent : observe wrongHelper 4 ≠ observe (linked prepared) 8 := by
  decide +kernel

/-- A RHS body that reads x is stuck: rhs(void) has no x parameter. The
caller pointer cannot supply ambient numerical locals. -/
def wrongKernel : Program := { linked prepared with kernel := ⟨.arg, .arg, .arg⟩ }

theorem changed_kernel_stuck : (run wrongKernel 8 start).isNone = true := by
  decide +kernel

theorem wrong_arity_rejected :
    (next (linked prepared) (.calling "model_rhs" [] heap .done)).isNone = true := by
  decide +kernel

theorem unknown_symbol_rejected :
    (next (linked prepared) (.calling "missing" [] heap .done)).isNone = true := by
  decide +kernel

theorem duplicate_parameters_rejected :
    (CCalls.parameters [⟨"int", "a", false⟩, ⟨"int", "a", false⟩]
      [.integer 0, .integer 1]).isNone = true := by
  decide +kernel

theorem nonfinite_kernel_input_rejected :
    (kernelEntry .step [.float64 (BitVec.ofNat 64 0x7ff0000000000000)]).isNone = true := by
  decide +kernel

theorem oversized_counter_rejected :
    (kernelEntry .sample [.finite Binary64.one, .integer (2 ^ 64)]).isNone = true := by
  decide +kernel

end Rumoca.FMI3.CallChecks

#audit axioms Rumoca.FMI3.CallChecks.linked_rhs_observed
#audit axioms Rumoca.FMI3.CallChecks.changed_helper_observed
#audit axioms Rumoca.FMI3.CallChecks.changed_helper_not_equivalent
#audit axioms Rumoca.FMI3.CallChecks.changed_kernel_stuck
#audit axioms Rumoca.FMI3.CallChecks.wrong_arity_rejected
#audit axioms Rumoca.FMI3.CallChecks.unknown_symbol_rejected
#audit axioms Rumoca.FMI3.CallChecks.duplicate_parameters_rejected
#audit axioms Rumoca.FMI3.CallChecks.nonfinite_kernel_input_rejected
#audit axioms Rumoca.FMI3.CallChecks.oversized_counter_rejected
