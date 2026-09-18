import RumocaC.Codegen
import RumocaCore.Constant.Semantics

/-! Numerical C for the G01 constant-rate profile: a state vector of `N`
binary64 doubles with a constant rate vector. `rumoca_constant_rhs` writes the
rates, `rumoca_constant_step` advances every state by one explicit Euler step,
and `rumoca_constant_sample` iterates that step a counted number of times. The
emission is universal in the number of states; the target semantics interpret
each rendered decimal literal as the round-to-nearest-even of its exact
base-ten content, and each step as the finite binary64 addition of that rate.
The array storage is caller-owned, so no dynamic allocation is emitted. -/
namespace Rumoca.CConstant
open Rumoca.ConstantProfile Rumoca.Binary64

/-! ### Rendering the numerical C, universal in the number of states -/

/-- A single base-ten digit character. Structural, so the kernel reduces it. -/
private def digitChar (n : Nat) : Char := Char.ofNat (48 + n % 10)

/-- The base-ten characters of a natural number, most significant first. The
first argument is a structural fuel bound; `natStr` supplies enough. Every step
uses only kernel-accelerated `Nat` arithmetic, so the whole render reduces under
`decide +kernel`, unlike the standard `toString`/`Nat.repr` path. -/
private def natChars : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n => if n < 10 then [digitChar n] else natChars fuel (n / 10) ++ [digitChar (n % 10)]

/-- Base-ten spelling of a natural number. -/
def natStr (n : Nat) : String := String.ofList (natChars (n + 1) n)

/-- Base-ten spelling of an integer, with a leading `-` for negatives. -/
def intStr (z : Int) : String := (if z < 0 then "-" else "") ++ natStr z.natAbs

/-- A C floating constant whose exact base-ten value is `sign * mantissa *
10 ^ power`. The mantissa and exponent record the literal content exactly, so a
conforming translator rounds the constant to the same binary64 value the target
contract specifies for the literal. -/
def renderRate (d : Decimal) : String :=
  (if d.sign < 0 then "-" else "") ++ natStr d.mantissa ++ "e" ++ intStr d.power

/-- One `der[i] = rate;` line, in declaration order. -/
def rhsFrom (start : Nat) : List Decimal → String
  | [] => ""
  | d :: ds =>
    "  der[" ++ natStr start ++ "] = " ++ renderRate d ++ ";\n" ++ rhsFrom (start + 1) ds

/-- One `x[i] = (x[i] + rate);` explicit Euler update, in declaration order.
`indent` distinguishes the top-level step body from the loop body. -/
def stepFrom (indent : String) (start : Nat) : List Decimal → String
  | [] => ""
  | d :: ds =>
    indent ++ "x[" ++ natStr start ++ "] = (x[" ++ natStr start ++ "] + " ++
      renderRate d ++ ");\n" ++ stepFrom indent (start + 1) ds

/-- The complete numerical C for a rate list. Function bodies read and write the
caller-owned arrays only; there is no allocation. -/
def renderRates (rates : List Decimal) : String :=
  Rumoca.C.preamble ++
  "void rumoca_constant_rhs(double *der) {\n" ++ rhsFrom 0 rates ++ "}\n\n" ++
  "void rumoca_constant_step(double *x) {\n" ++ stepFrom "  " 0 rates ++ "}\n\n" ++
  "void rumoca_constant_sample(double *x, uint64_t n) {\n" ++
  "  while (n != 0) {\n" ++ stepFrom "    " 0 rates ++
  "    n = n - UINT64_C(1);\n  }\n}\n"

/-- The numerical C of a prepared multi-state IVP, in declaration order. -/
def _root_.Rumoca.ConstantProfile.ConstantIVP.render (ivp : ConstantIVP n) : String :=
  renderRates (List.ofFn ivp.rates)

/-- A rate list assembled into an IVP of matching length. -/
def _root_.Rumoca.ConstantProfile.ConstantIVP.ofList (rates : List Decimal) :
    ConstantIVP rates.length := ⟨fun i => rates.get i⟩

theorem render_ofList (rates : List Decimal) :
    (ConstantIVP.ofList rates).render = renderRates rates := by
  simp only [ConstantIVP.render, ConstantIVP.ofList, List.ofFn_get]

/-! ### Finite binary64 semantics of the emitted kernel -/

/-- One explicit Euler step of a whole state vector: each state is advanced by
the finite binary64 addition of its constant rate. -/
noncomputable def stepState (ivp : ConstantIVP n) (x : Fin n → Value) : Fin n → Value :=
  fun i => roundedAdd (x i) (ivp.rateValues i)

/-- Iterating the whole-vector Euler step `k` times. -/
noncomputable def runState (ivp : ConstantIVP n) (x : Fin n → Value) : Nat → (Fin n → Value)
  | 0 => x
  | k + 1 => runState ivp (stepState ivp x) k

/-- One state's independent constant-rate Euler trajectory. -/
noncomputable def runBy (r x : Value) : Nat → Value
  | 0 => x
  | k + 1 => runBy r (roundedAdd x r) k

/-- The states are independent: the whole-vector iteration equals each state's
own constant-rate trajectory, for every start vector and step count. -/
theorem runState_pointwise (ivp : ConstantIVP n) (x : Fin n → Value) (k : Nat) (i : Fin n) :
    runState ivp x k i = runBy (ivp.rateValues i) (x i) k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [runState, runBy, ih, stepState]

/-- The counted-step execution relation of `rumoca_constant_sample`. -/
inductive SampleExec (ivp : ConstantIVP n) : (Fin n → Value) → Nat → (Fin n → Value) → Prop where
  | done (x) : SampleExec ivp x 0 x
  | more (x k out) : SampleExec ivp (stepState ivp x) k out → SampleExec ivp x (k + 1) out

theorem sample_correct (ivp : ConstantIVP n) (x : Fin n → Value) (k : Nat) :
    SampleExec ivp x k (runState ivp x k) := by
  induction k generalizing x with
  | zero => exact .done x
  | succ k ih => exact .more x k _ (ih _)

theorem sample_deterministic {ivp : ConstantIVP n} {x : Fin n → Value} {k : Nat} {a b : Fin n → Value}
    (h₁ : SampleExec ivp x k a) (h₂ : SampleExec ivp x k b) : a = b := by
  induction h₁ with
  | done => cases h₂; rfl
  | more _ _ _ _ ih => cases h₂ with | more _ _ _ h => exact ih h

/-! ### The actual-artifact contract -/

/-- The target execution and rounding contract for the constant-rate kernel:
the emitted bytes are the rendered numerical C; every state initializes at `+0`;
`rumoca_constant_rhs` writes each state's rate, which is the round-to-nearest-even
of the exact base-ten content of its decimal literal; `rumoca_constant_step`
is the finite binary64 Euler update; and `rumoca_constant_sample` executes the
counted iteration, whose result is each state's independent trajectory. -/
structure Contract (ivp : ConstantIVP n) (emitted : String) : Prop where
  bytes : ivp.render = emitted
  initial_zero : ∀ i, ivp.initial i = positiveZero
  rates_rounded : ∀ i, Scaled.RoundsNearestEven (ivp.rates i).scale (ivp.rates i).numerator
    (ivp.rateValues i)
  step_is_euler : ∀ x i, stepState ivp x i = roundedAdd (x i) (ivp.rateValues i)
  sample_exec : ∀ x k, SampleExec ivp x k (runState ivp x k)
  sample_trajectory : ∀ x k i, runState ivp x k i = runBy (ivp.rateValues i) (x i) k

/-- Every prepared constant-rate IVP satisfies the contract for its rendered
numerical C. Universal in the number of states. -/
theorem contract_correct (ivp : ConstantIVP n) (emitted : String) (h : ivp.render = emitted) :
    Contract ivp emitted :=
  ⟨h, fun _ => rfl, fun i => (ivp.rates i).rate_rounds, fun _ _ => rfl,
    sample_correct ivp, runState_pointwise ivp⟩

/-- The renderer reduces under the kernel, so a fixed emission can be checked
against actual bytes by `decide +kernel`. -/
example : natStr 25 = "25" := by decide +kernel
example : intStr (-1) = "-1" := by decide +kernel
example : renderRate ⟨1, 25, -1⟩ = "25e-1" := by decide +kernel
example : renderRate ⟨-1, 1, 0⟩ = "-1e0" := by decide +kernel

end Rumoca.CConstant
