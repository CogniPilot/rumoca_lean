import RumocaC.Calls
import RumocaCore.Real.Multiplication

/-! The straight-line C arithmetic extension needed by Solve register code.
Other statements retain the existing object-memory semantics. The arithmetic
operations are finite binary64 addition and multiplication in an initializer; compound
arithmetic expressions, nonfinite operands and overflow remain unsupported.
Generated unit-method proofs establish that all their additions are in domain. -/
noncomputable section
namespace Rumoca.CArithmetic
open Rumoca.CTree Rumoca.CMemory

def floatAdd (left right : Value) : Option Value := do
  let x ← CCalls.finiteValue left
  let y ← CCalls.finiteValue right
  if Rumoca.CExecution.finiteRoundDomain (Binary64.units x + Binary64.units y) then
    return .finite (Binary64.roundedAdd x y)
  else none

theorem floatAdd_finite (x y : Binary64.Value)
    (h : Rumoca.CExecution.finiteRoundDomain (Binary64.units x + Binary64.units y)) :
    floatAdd (.finite x) (.finite y) = some (.finite (Binary64.roundedAdd x y)) := by
  simp only [floatAdd, CCalls.finiteValue_finite, bind, Option.bind_some, if_pos h, pure]

theorem floatAdd_one (x : Binary64.Value) :
    floatAdd (.finite x) (.finite Binary64.one) = some (.finite (Binary64.advance x)) := by
  rw [floatAdd_finite x Binary64.one]
  · rw [Binary64.roundedAdd_one]
  · rw [Binary64.units_one]
    exact Binary64.advance_no_overflow x

def floatMul (left right : Value) : Option Value := do
  let x ← CCalls.finiteValue left
  let y ← CCalls.finiteValue right
  return .finite (← Binary64.multiply? x y)

theorem floatMul_finite (x y : Binary64.Value) (h : Binary64.finiteProduct x y) :
    floatMul (.finite x) (.finite y) = some (.finite (Binary64.roundedMul x y)) := by
  simp only [floatMul, CCalls.finiteValue_finite, Binary64.multiply?, if_pos h,
    bind, Option.bind_some, pure]

variable [interface : CInterface]

def next : CBody.State → Option CBody.State
  | .running (.declare type name (.bin .add a b) :: rest) env heap => do
      let value ← floatAdd (← CBody.eval env heap a) (← CBody.eval env heap b)
      let converted ← CBody.cast type value
      if (env name).isSome then none else
        return .running rest (CBody.bind env name converted) heap
  | .running (.declare type name (.bin .mul a b) :: rest) env heap => do
      let value ← floatMul (← CBody.eval env heap a) (← CBody.eval env heap b)
      let converted ← CBody.cast type value
      if (env name).isSome then none else
        return .running rest (CBody.bind env name converted) heap
  | state => CBody.next state

def machine : Transition.Machine CBody.State CBody.Result where
  step s t := next s = some t
  final | .returned result => some result | _ => none
  deterministic ha hb := Option.some.inj (ha.symm.trans hb)
  final_stuck := by
    intro s result hs t
    cases s <;> simp_all [next, CBody.next]

def run : Nat → CBody.State → Option CBody.State
  | 0, state => some state
  | n + 1, state => do run n (← next state)

theorem run_reaches (h : run n s = some t) : Transition.Reaches machine.step s t := by
  induction n generalizing s with
  | zero => cases Option.some.inj h; exact .refl _
  | succ n ih =>
    cases hn : next s with
    | none => simp [run, hn] at h
    | some u =>
      simp only [run, hn] at h
      exact .next hn (ih h)

theorem behaviors_of_run (h : run n s = some (.returned result)) (behavior) :
    machine.Behaves s behavior ↔ behavior = .terminates result :=
  machine.behavior_iff (run_reaches h) rfl

end Rumoca.CArithmetic
