import RumocaFMI3.Runtime

/-! Semantics for the integer/Boolean fragment used by the generated lifecycle
guards. The two readable fields represent a valid instance's kind and mode.
This bridge covers the constructed guard AST, not C pointer validity, the
printer, function bodies, allocation, or native machine execution. -/
namespace Rumoca.FMI3
open CTree

def guardEval (kind mode : Nat) : Expr → Option Nat
  | .nat n => some n
  | .field (.id "m") "kind" true => some kind
  | .field (.id "m") "mode" true => some mode
  | .bin .eq a b => do return if (← guardEval kind mode a) = (← guardEval kind mode b) then 1 else 0
  | .bin .and a b => do
    if (← guardEval kind mode a) = 0 then return 0
    return if (← guardEval kind mode b) = 0 then 0 else 1
  | .bin .or a b => do
    if (← guardEval kind mode a) ≠ 0 then return 1
    return if (← guardEval kind mode b) = 0 then 0 else 1
  | .not a => do return if (← guardEval kind mode a) = 0 then 1 else 0
  | _ => none

def Kind.code : Kind → Nat | .me => 0 | .cs => 1

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem guard_correct (c : Command) (k : Kind) (m : Mode) :
    guardEval k.code m.code (Runtime.allowedExpression c) =
      some (if allowed c k m then 1 else 0) := by
  cases c <;> cases k <;> cases m <;> decide +kernel

theorem guard_reference (c : Command) (k : Kind) (m : Mode) :
    guardEval k.code m.code (Runtime.allowedExpression c) = some 1 ↔
      Reference.Allowed c k m := by
  rw [guard_correct, ← allowed_correct]
  cases allowed c k m <;> decide

end Rumoca.FMI3
