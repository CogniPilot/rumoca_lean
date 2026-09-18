import ModelicaParser.Constant.Located
import RumocaCore.Real.ScaledRounding

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

/-- The rounded binary64 rate assigned to a state. -/
noncomputable def Model.rateOf (m : Model) (state : String) : Value := (m.decimalOf state).rate

/-! ### The prepared constant-rate initial value problem -/

/-- A multi-state IVP with one constant literal rate per state, in declaration
order, and zero initial state. The stored literals are computable; the binary64
rate values are the exact rounding of that content. -/
structure ConstantIVP (n : Nat) where
  rates : Fin n → Decimal

/-- The exactly rounded binary64 rate vector of the IVP. -/
noncomputable def ConstantIVP.rateValues (ivp : ConstantIVP n) : Fin n → Value :=
  fun i => (ivp.rates i).rate

def ConstantIVP.initial (_ : ConstantIVP n) : Fin n → Value := fun _ => positiveZero

/-- Lowering to the executable multi-state IVP: one literal per declared state,
in declaration order. -/
def Model.lower (m : Model) : ConstantIVP m.states.length :=
  ⟨fun i => m.decimalOf (m.states.get i)⟩

theorem Model.lower_rate (m : Model) (i : Fin m.states.length) :
    (m.lower).rateValues i = m.rateOf (m.states.get i) := rfl

/-! ### Source semantics and the lowering chain -/

/-- The source system: each declared state's derivative is its rounded rate. -/
def Model.Solves (m : Model) (derivatives : String → Value) : Prop :=
  ∀ state ∈ m.states, derivatives state = m.rateOf state

/-- The declarations carry no start modifier, so every state initializes at
`+0`, as in the unit and array profiles. -/
def Model.Initial (m : Model) (values : String → Value) : Prop :=
  ∀ state ∈ m.states, values state = positiveZero

theorem Model.lowering_chain (m : Model) (derivatives : String → Value) :
    m.Solves derivatives ↔
      ∀ i : Fin m.states.length, derivatives (m.states.get i) = (m.lower).rateValues i := by
  constructor
  · intro h i; rw [m.lower_rate]; exact h _ (m.states.get_mem i)
  · intro h state hmem
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    simpa [m.lower_rate] using h i

theorem Model.initialization_chain (m : Model) (values : String → Value) :
    m.Initial values ↔
      ∀ i : Fin m.states.length, values (m.states.get i) = (m.lower).initial i := by
  constructor
  · intro h i; exact h _ (m.states.get_mem i)
  · intro h state hmem
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    exact h i

end Rumoca.ConstantProfile
