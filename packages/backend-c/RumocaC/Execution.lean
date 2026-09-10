import RumocaC.Syntax
import RumocaCore.Real.Binary64
import RumocaCore.Profile

/-! Whole-iteration abstraction for finite arithmetic and countdown algebra.
The double primitive uses the exact binary64 specification. This abstraction
does not model local scope or individual statements; CStatements supplies the
independent scoped target semantics used by the high-level compiler theorem. -/
noncomputable section
namespace Rumoca.CExecution
open Binary64

abbrev finiteRoundDomain (z : Int) : Prop :=
  -(maxUnits + 2 ^ 2044 : Int) < z ∧ z < (maxUnits + 2 ^ 2044 : Int)

/-- Overflow is outside the admitted finite-double expression profile. The
compiler theorem proves it cannot occur for any finite x in x+1. -/
def eval (x : Value) : C.Expr → Option Value
  | .one => some one
  | .arg => some x
  | .add a b => do
    let av ← eval x a
    let bv ← eval x b
    let sum := units av + units bv
    if finiteRoundDomain sum then some (roundedAdd av bv) else none

theorem rhs_eval (m : Solve.Model source) (x : Value) : eval x (C.lower m).rhs = some one := by
  rw [C.lower_is_unit]
  rfl

theorem step_eval (m : Solve.Model source) (x : Value) :
    eval x (C.lower m).step = some (advance x) := by
  rw [C.lower_is_unit]
  simp only [C.Module.step, C.unitModule, eval, bind, Option.bind_some, units_one]
  rw [if_pos (advance_no_overflow x)]
  rw [roundedAdd_one]

abbrev Function := Profile.Function

inductive State where
  | entry (function : Function) (x : Value) (n : Nat)
  | loop (x : Value) (n : Nat)
  | returned (x : Value)

/-- One body iteration includes expression evaluation, assignment, and the
nonzero unsigned decrement, in C's specified sequence. -/
inductive Step (p : CSyntax.Program) : State → State → Prop where
  | rhs : eval x p.rhs = some y → Step p (.entry .rhs x n) (.returned y)
  | step : eval x p.step = some y → Step p (.entry .step x n) (.returned y)
  | enter : Step p (.entry .sample x n) (.loop x n)
  | stop : Step p (.loop x 0) (.returned x)
  | next : eval x p.sample = some y → Step p (.loop x (n + 1)) (.loop y n)

inductive Reaches (p : CSyntax.Program) : State → State → Prop where
  | refl (s) : Reaches p s s
  | next : Step p s t → Reaches p t u → Reaches p s u

theorem step_deterministic (ha : Step p s a) (hb : Step p s b) : a = b := by
  cases ha <;> cases hb <;> simp_all

theorem reaches_trans (h₁ : Reaches p s t) (h₂ : Reaches p t u) : Reaches p s u := by
  induction h₁ with
  | refl => exact h₂
  | next h _ ih => exact .next h (ih h₂)

def program (m : Solve.Model source) : CSyntax.Program := CSyntax.fromTarget (C.lower m)

private theorem loop_reaches (m : Solve.Model source) (x : Value) (n : Nat) :
    Reaches (program m) (.loop x n) (.returned (run x n)) := by
  induction n generalizing x with
  | zero => exact .next .stop (.refl _)
  | succ n ih => exact .next (.next (step_eval m x)) (ih (advance x))

theorem sample_reaches (m : Solve.Model source) (x : Value) (n : Nat) :
    Reaches (program m) (.entry .sample x n) (.returned (run x n)) :=
  .next .enter (loop_reaches m x n)

private def result : State → Value
  | .entry .rhs _ _ => one
  | .entry .step x _ => advance x
  | .entry .sample x n => run x n
  | .loop x n => run x n
  | .returned x => x

private theorem step_result (m : Solve.Model source) (h : Step (program m) s t) : result s = result t := by
  cases h with
  | rhs h =>
    have he := (rhs_eval m _).symm.trans h
    exact Option.some.inj he
  | step h =>
    have he := (step_eval m _).symm.trans h
    exact Option.some.inj he
  | enter => rfl
  | stop => rfl
  | next h =>
    have he := (step_eval m _).symm.trans h
    cases Option.some.inj he
    rfl

private theorem reaches_result (m : Solve.Model source) (h : Reaches (program m) s t) : result s = result t := by
  induction h with
  | refl => rfl
  | next h _ ih => exact (step_result m h).trans ih

private theorem returned_accessible (p : CSyntax.Program) (x : Value) :
    Acc (fun t s => Step p s t) (.returned x) := by
  constructor
  intro s h
  cases h

private theorem loop_accessible (m : Solve.Model source) (x : Value) (n : Nat) :
    Acc (fun t s => Step (program m) s t) (.loop x n) := by
  induction n generalizing x with
  | zero =>
    constructor
    intro s h
    cases h
    exact returned_accessible _ _
  | succ n ih =>
    constructor
    intro s h
    cases h with
    | next h => exact ih _

/-- Accessibility rules out every infinite reduction sequence. This proves
termination for every possible execution, not just a selected path. -/
theorem sample_accessible (m : Solve.Model source) (x : Value) (n : Nat) :
    Acc (fun t s => Step (program m) s t) (.entry .sample x n) := by
  constructor
  intro s h
  cases h
  exact loop_accessible m x n

private theorem state_finishes (m : Solve.Model source) (s : State) :
    Reaches (program m) s (.returned (result s)) := by
  cases s with
  | returned x => exact .refl _
  | loop x n => exact loop_reaches m x n
  | entry f x n =>
    cases f with
    | rhs => exact .next (.rhs (rhs_eval m x)) (.refl _)
    | step => exact .next (.step (step_eval m x)) (.refl _)
    | sample => exact sample_reaches m x n

/-- No reachable state can be stuck before the unique returned value. -/
theorem sample_all_executions (m : Solve.Model source) (x : Value) (n : Nat)
    (h : Reaches (program m) (.entry .sample x n) s) :
    Reaches (program m) s (.returned (run x n)) := by
  have he := reaches_result m h
  change run x n = result s at he
  rw [he]
  exact state_finishes m s

theorem sample_result_unique (m : Solve.Model source) (x : Value) (n : Nat)
    (h : Reaches (program m) (.entry .sample x n) (.returned y)) : y = run x n :=
  (reaches_result m h).symm

/-- The native unsigned counter never wraps: decrement is reached only when
positive. It is control data, not the Modelica Real state. -/
def counter : State → Nat
  | .entry _ _ n | .loop _ n => n
  | .returned _ => 0

theorem counter_nonincreasing (h : Step p s t) : counter t ≤ counter s := by
  cases h <;> simp [counter]

theorem counter_in_range (h : Reaches p s t) (hn : counter s < 2 ^ 64) : counter t < 2 ^ 64 := by
  induction h with
  | refl => exact hn
  | next h _ ih => exact ih (lt_of_le_of_lt (counter_nonincreasing h) hn)

end Rumoca.CExecution
