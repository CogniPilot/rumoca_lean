import RumocaCore.GALEC.BoundedIteration

/-! Restricted ascending unit-range semantics. Iterator values are mathematical
Integers, independently of the bounded-index execution relation. This does not
define arbitrary GALEC for-loops, source elaboration, or machine counters.
The zero case is a semantic empty range, not zero-size source admission. -/
namespace Rumoca.GALEC.IntegerIteration

universe u
variable {σ : Type u}

/-- Execute the Integer values `1, ..., count`, in this order. No totality or
determinism is imposed on the body relation; every constructor retains its
actual intermediate state. -/
inductive Executes (step : Int → σ → σ → Prop) : Nat → σ → σ → Prop where
  | zero (state) : Executes step 0 state state
  | next {count initial before after}
      (earlier : Executes step count initial before)
      (body : step (Int.ofNat count + 1) before after) :
      Executes step (count + 1) initial after

/-- Change only the iterator representation for any bounded prefix. Both
directions reuse exactly the constructor's `before` state and body witness. -/
theorem executes_prefix_iff (step : Int → σ → σ → Prop)
    (n count : Nat) (within : count ≤ n) (initial final : σ) :
    Executes step count initial final ↔
      Rumoca.GALEC.Iteration.Executes
        (fun i : Fin n => step (Int.ofNat i.val + 1)) count initial final := by
  induction count generalizing final with
  | zero =>
    constructor
    · intro h; cases h; exact .zero initial
    · intro h; cases h; exact .zero initial
  | succ count ih =>
    constructor
    · intro h
      cases h with
      | next earlier body =>
        exact .next (Nat.lt_of_succ_le within)
          ((ih (Nat.le_of_succ_le within) _).mp earlier) body
    · intro h
      cases h with
      | next hk earlier body =>
        exact .next ((ih (Nat.le_of_lt hk) _).mpr earlier) body

/-- Universal complete-range bridge, including `n = 0`, for arbitrary partial
or nondeterministic bodies and every pair of endpoint states. -/
theorem executes_iff (step : Int → σ → σ → Prop) (n : Nat) (initial final : σ) :
    Executes step n initial final ↔
      Rumoca.GALEC.Iteration.Executes
        (fun i : Fin n => step (Int.ofNat i.val + 1)) n initial final :=
  executes_prefix_iff step n n (Nat.le_refl _) initial final

/-- Every active iterator value lies in `1..n` and below the explicitly supplied
Integer ceiling. No fixed bit width, post-loop increment, or target arithmetic
is assumed. For `n = 0` there are no active indices. -/
theorem one_based_representable (n : Nat) (maxInteger : Int)
    (fits : Int.ofNat n ≤ maxInteger) (i : Fin n) :
    1 ≤ Int.ofNat i.val + 1 ∧ Int.ofNat i.val + 1 ≤ Int.ofNat n ∧
      Int.ofNat i.val + 1 ≤ maxInteger := by
  have bounds := Rumoca.GALEC.Iteration.one_based_bounds i
  change (n : Int) ≤ maxInteger at fits
  change 1 ≤ (i.val : Int) + 1 ∧ (i.val : Int) + 1 ≤ (n : Int) ∧
    (i.val : Int) + 1 ≤ maxInteger
  omega

/-- An in-range mathematical Integer determines exactly one bounded index.
This is a value-level inverse, not source-name resolution or scope checking. -/
theorem one_based_unique (n : Nat) (value : Int)
    (positive : 1 ≤ value) (within : value ≤ Int.ofNat n) :
    ∃! i : Fin n, Int.ofNat i.val + 1 = value := by
  have nonnegative : 0 ≤ value - 1 := by omega
  have converted : Int.ofNat (value - 1).toNat = value - 1 :=
    Int.toNat_of_nonneg nonnegative
  change (n : Int) ≥ value at within
  change ((value - 1).toNat : Int) = value - 1 at converted
  refine ⟨⟨(value - 1).toNat, by omega⟩, ?_, ?_⟩
  · change ((value - 1).toNat : Int) + 1 = value
    omega
  · intro other same
    change (other.val : Int) + 1 = value at same
    apply Fin.ext
    change other.val = (value - 1).toNat
    omega

end Rumoca.GALEC.IntegerIteration
