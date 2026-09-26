import ModelicaParser.Constant.Located
import RumocaCore.Real.ScaledRounding
import RumocaCore.Initialization.Scalar

/-! Source semantics and Solve lowering for the G01 constant-rate profile: a
system of independent states whose derivatives are constant, one per declared
state, in declaration order. Each rate is the exactly rounded binary64 value of
its decimal literal. The prepared IVP keeps the computable literal content; the
binary64 value is the round-to-nearest-even of that content, a target contract.
The equation order is immaterial: a state's rate depends only on the equation
that names it. -/
namespace Rumoca.ConstantProfile
open Rumoca.Binary64

/-! ### Exact binary64 rounding of a decimal literal -/

/-- The positive denominator that places the literal on the binary64 grid. -/
def Decimal.scale (d : Decimal) : Nat :=
  if d.power < 0 then 10 ^ (-d.power).toNat else 1

/-- The integer numerator measured in units of `2^-1074`. -/
def Decimal.numerator (d : Decimal) : Int :=
  if d.power < 0 then d.sign * (d.mantissa : Int) * (oneUnits : Int)
  else d.sign * (d.mantissa : Int) * (10 : Int) ^ d.power.toNat * (oneUnits : Int)

/-- The exactly rounded binary64 rate of the literal (a real-valued target). -/
noncomputable def Decimal.rate (d : Decimal) : Value := Scaled.round d.scale d.numerator

theorem Decimal.scale_pos (d : Decimal) : 0 < d.scale := by
  unfold Decimal.scale; split
  · exact pow_pos (by decide) _
  · decide

/-- Every literal's stored rate is the round-to-nearest-even of its exact
base-ten value on the finite binary64 grid. This is the exact-rounding
obligation for the profile, discharged uniformly by the scaled rounding spec. -/
theorem Decimal.rate_rounds (d : Decimal) :
    Scaled.RoundsNearestEven d.scale d.numerator d.rate :=
  Scaled.round_spec d.scale d.numerator

/-! ### Literal of a declared state -/

/-- The equation that names `state`, if any. -/
def Model.equationFor (m : Model) (state : String) : Option Equation :=
  m.equations.find? (fun e => e.derivative == state)

/-- The decimal literal assigned to a state. Unresolved names fall back to `0`;
resolution rules them out for the states of an admitted model. -/
def Model.decimalOf (m : Model) (state : String) : Decimal :=
  match (m.equationFor state).bind (fun e => parseDecimal e.rate) with
  | some d => d
  | none => ⟨1, 0, 0⟩

/-- Resolution admits the magnitude of every declared state's rate literal. -/
theorem Model.decimalOf_admitted (m : Model) (h : m.Resolved) (state : String)
    (mem : state ∈ m.states) : (m.decimalOf state).admitted = true := by
  obtain ⟨e, he, hname⟩ := List.mem_map.mp (h.2.2.1.mem_iff.mpr mem)
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨e, he, by simp [hname]⟩ :
      (m.equations.find? (fun e => e.derivative == state)).isSome)
  have rate := h.2.2.2 found (List.mem_of_find?_eq_some hfound)
  unfold Model.decimalOf Model.equationFor
  rw [hfound, Option.bind_some]
  cases hp : parseDecimal found.rate with
  | none => rw [hp] at rate; simp at rate
  | some d => rw [hp] at rate; simpa using rate

/-- The rounded binary64 rate assigned to a state. -/
noncomputable def Model.rateOf (m : Model) (state : String) : Value := (m.decimalOf state).rate

/-! ### Initialization (MLS 3.7 §8.6, Definition 4.7)

Every declaration is an unmodified `Real`: no binding, no start modifier and not
fixed. Its start value is the Real fallback `0`, which by itself adds no initial
equation, so the source leaves every initial state free. The compiler completes
each state through the shared `Initialization.prepare`, selecting the fallback
as fixed and recording both notices. -/

/-- The initialization settings of a declared state: no binding, no start and
not fixed. -/
def Model.settings (_ : Model) (_ : String) : Initialization.Settings Nat := {}

/-- The completed initialization of a declared state: the checked preparation of
its settings with the Real fallback `0`. -/
def Model.plan (m : Model) (state : String) : Initialization.Plan Nat :=
  (Initialization.checked (m.settings state) 0 ⟨_, Initialization.prepare_default 0⟩).val

theorem Model.plan_prepared (m : Model) (state : String) :
    Initialization.prepare (m.settings state) 0 = .ok (m.plan state) :=
  (Initialization.checked (m.settings state) 0 ⟨_, Initialization.prepare_default 0⟩).property

/-- Each state starts from the fallback `0` with both §8.6 notices: the fallback
start is used and the unfixed start is selected as fixed. -/
theorem Model.plan_default (m : Model) (state : String) :
    m.plan state = ⟨0, [.fallbackUsed, .unfixedStartSelected]⟩ := rfl

/-! ### The prepared constant-rate initial value problem -/

/-- A multi-state IVP with one constant literal rate and one completed start
value per state, in declaration order. The stored literals and starts are
computable; the binary64 values are the exact rounding of that content. -/
structure ConstantIVP (n : Nat) where
  rates : Fin n → Decimal
  starts : Fin n → Nat

/-- The exactly rounded binary64 rate vector of the IVP. -/
noncomputable def ConstantIVP.rateValues (ivp : ConstantIVP n) : Fin n → Value :=
  fun i => (ivp.rates i).rate

/-- The exactly rounded binary64 value of a natural start value. -/
noncomputable def startBinary (start : Nat) : Value := (⟨1, start, 0⟩ : Decimal).rate

/-- The start `0` is stored as `+0`. -/
theorem startBinary_zero : startBinary 0 = positiveZero := by
  unfold startBinary Decimal.rate Decimal.numerator
  simpa using Scaled.round_zero (⟨1, 0, 0⟩ : Decimal).scale

/-- The completed binary64 initial state of the IVP. -/
noncomputable def ConstantIVP.initial (ivp : ConstantIVP n) : Fin n → Value :=
  fun i => startBinary (ivp.starts i)

/-- Lowering to the executable multi-state IVP: one literal and the completed plan
start per declared state, in declaration order. -/
def Model.lower (m : Model) : ConstantIVP m.states.length :=
  ⟨fun i => m.decimalOf (m.states.get i), fun i => (m.plan (m.states.get i)).initial⟩

theorem Model.lower_rate (m : Model) (i : Fin m.states.length) :
    (m.lower).rateValues i = m.rateOf (m.states.get i) := rfl

/-- Every literal of the lowered IVP has an admitted magnitude. -/
theorem Model.lower_admitted (m : Model) (h : m.Resolved) (i : Fin m.states.length) :
    (m.lower.rates i).admitted = true :=
  m.decimalOf_admitted h _ (m.states.get_mem i)

/-! ### Source semantics and the lowering chain -/

/-- The source system: each declared state's derivative is its rounded rate. -/
def Model.Solves (m : Model) (derivatives : String → Value) : Prop :=
  ∀ state ∈ m.states, derivatives state = m.rateOf state

/-- The binary64 start value of a declared state, from its completed plan. -/
noncomputable def Model.startValue (m : Model) (state : String) : Value :=
  startBinary (m.plan state).initial

/-- Every completed start is the fallback `0`, stored as `+0`. -/
theorem Model.startValue_default (m : Model) (state : String) : m.startValue state = positiveZero := by
  rw [Model.startValue, Model.plan_default]; exact startBinary_zero

/-- The source initialization relation: a state is constrained only when its
start is fixed, and then to that start. No declaration of this profile is
fixed. -/
def Model.Initial (m : Model) (values : String → Value) : Prop :=
  ∀ state ∈ m.states, (m.settings state).fixed = true →
    values state = startBinary ((m.settings state).startValue 0)

/-- The source leaves every initial state free. -/
theorem Model.initial_free (m : Model) (values : String → Value) : m.Initial values :=
  fun _ _ fixed => nomatch fixed

/-- The completed initialization: every state starts at the binary64 value of
its completed plan start. -/
def Model.Completed (m : Model) (values : String → Value) : Prop :=
  ∀ state ∈ m.states, values state = m.startValue state

theorem Model.completed_initial (m : Model) (values : String → Value) (_ : m.Completed values) :
    m.Initial values := m.initial_free values

theorem Model.lowering_chain (m : Model) (derivatives : String → Value) :
    m.Solves derivatives ↔
      ∀ i : Fin m.states.length, derivatives (m.states.get i) = (m.lower).rateValues i := by
  constructor
  · intro h i; rw [m.lower_rate]; exact h _ (m.states.get_mem i)
  · intro h state hmem
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    simpa [m.lower_rate] using h i

theorem Model.initialization_chain (m : Model) (values : String → Value) :
    m.Completed values ↔
      ∀ i : Fin m.states.length, values (m.states.get i) = (m.lower).initial i := by
  constructor
  · intro h i; exact h _ (m.states.get_mem i)
  · intro h state hmem
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    exact h i

end Rumoca.ConstantProfile
