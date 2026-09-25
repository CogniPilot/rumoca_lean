import RumocaCore.GALEC.Statements
import RumocaCore.Real.NumberArithmetic
import RumocaCore.Solve.Tensor.Finite

/-! The meaning of the builtin `isFinite` on the complete IEEE binary64 domain,
and its agreement with partial finite arithmetic. A term built from the
admitted operators `+` and `*` has a finite IEEE result exactly when its
ordered finite evaluation succeeds, with the same result: a non-finite
intermediate never becomes finite again under `+` or `*`. This fails for
division (`x / inf = 0`), so the operator set is an explicit hypothesis. -/
noncomputable section
namespace Rumoca.GALEC
open Rumoca.Tensor Rumoca.Solve.Tensor

/-- IEEE results of the admitted binary operators on the complete domain. -/
def numberStep : BinaryOp → Float64.Number → Float64.Number → Float64.Number → Prop
  | .add, a, b, result => result = a.add b
  | .mul, a, b, result => result = a.mul b
  | .sub, _, _, _ | .div, _, _, _ => False

/-- The term uses only the admitted operators `+` and `*`. -/
def ScalarTerm.Admitted : ScalarTerm inputs outputs bounds → Prop
  | .literal _ | .input .. | .output .. => True
  | .binary op left right => (op = .add ∨ op = .mul) ∧ left.Admitted ∧ right.Admitted

/-- Finite stored values seen in the complete numerical domain. -/
def Env.numbers (env : Env Binary64.Value Γ) : Env Float64.Number Γ :=
  fun ref => (env ref).mapWith .finite

theorem ScalarTerm.evaluates_literal (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (iterators : IteratorEnv bounds)
    (value : Literal) (result : α) :
    (ScalarTerm.literal (outputs := outputs) (inputs := inputs) value).Evaluates step zero one
        @input @state iterators result ↔ result = value.eval zero one := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .literal value

theorem ScalarTerm.evaluates_input (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (iterators : IteratorEnv bounds)
    (ref : Ref inputs shape) (indices : Subscripts bounds shape.dimensions) (result : α) :
    (ScalarTerm.input (outputs := outputs) ref indices).Evaluates step zero one
        @input @state iterators result ↔
      result = (input ref)[Coordinate.index (indices.eval iterators)] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .input ref indices

theorem ScalarTerm.evaluates_output (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (iterators : IteratorEnv bounds)
    (ref : Ref outputs shape) (indices : Subscripts bounds shape.dimensions) (result : α) :
    (ScalarTerm.output (inputs := inputs) ref indices).Evaluates step zero one
        @input @state iterators result ↔
      result = (state ref)[Coordinate.index (indices.eval iterators)] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .output ref indices

theorem ScalarTerm.evaluates_binary (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (iterators : IteratorEnv bounds)
    (op : BinaryOp) (left right : ScalarTerm inputs outputs bounds) (result : α) :
    (ScalarTerm.binary op left right).Evaluates step zero one @input @state iterators result ↔
      ∃ a b, left.Evaluates step zero one @input @state iterators a ∧
        right.Evaluates step zero one @input @state iterators b ∧ step op a b result := by
  constructor
  · intro h; cases h with
    | binary l r s => exact ⟨_, _, l, r, s⟩
  · rintro ⟨a, b, l, r, s⟩; exact .binary l r s

theorem finite_add_iff (a b result : Binary64.Value) :
    Finite.Result .add a b result ↔ Binary64.addResult a b = .finite result := by
  rw [Finite.result_iff, Float64.addResult_finite_iff]
  rfl

theorem finite_mul_iff (a b result : Binary64.Value) :
    Finite.Result .mul a b result ↔ Binary64.mulResult a b = .finite result := by
  rw [Binary64.mulResult_finite_iff, Binary64.multiply_correct]
  rfl

/-- `number_eval_finite_iff`: for every term over the admitted operators, the
IEEE evaluation of the same term on the same finite stores yields the finite
value `result` exactly when ordered finite evaluation yields `result`. -/
theorem ScalarTerm.number_eval_finite_iff (term : ScalarTerm inputs outputs bounds)
    (admitted : term.Admitted) (zero one : Binary64.Value)
    (input : Env Binary64.Value inputs) (state : Env Binary64.Value outputs)
    (iterators : IteratorEnv bounds) (result : Binary64.Value) :
    term.Evaluates numberStep (.finite zero) (.finite one) (Env.numbers @input)
        (Env.numbers @state) iterators (.finite result) ↔
      term.Evaluates Finite.Result zero one @input @state iterators result := by
  induction term generalizing result with
  | literal value =>
    rw [evaluates_literal, evaluates_literal]
    cases value <;> simp [Literal.eval, eq_comm]
  | input ref indices =>
    rw [evaluates_input, evaluates_input]
    simp [Env.numbers]
  | output ref indices =>
    rw [evaluates_output, evaluates_output]
    simp [Env.numbers]
  | binary op left right ihl ihr =>
    obtain ⟨operator, leftAdmitted, rightAdmitted⟩ := admitted
    rw [evaluates_binary, evaluates_binary]
    constructor
    · rintro ⟨a, b, leftValue, rightValue, arithmetic⟩
      rcases operator with rfl | rfl
      · obtain ⟨x, y, rfl, rfl, sum⟩ := (Float64.Number.add_finite_iff a b result).mp arithmetic.symm
        exact ⟨x, y, (ihl leftAdmitted x).mp leftValue, (ihr rightAdmitted y).mp rightValue,
          (finite_add_iff x y result).mpr sum⟩
      · obtain ⟨x, y, rfl, rfl, product⟩ :=
          (Float64.Number.mul_finite_iff a b result).mp arithmetic.symm
        exact ⟨x, y, (ihl leftAdmitted x).mp leftValue, (ihr rightAdmitted y).mp rightValue,
          (finite_mul_iff x y result).mpr product⟩
    · rintro ⟨x, y, leftValue, rightValue, arithmetic⟩
      refine ⟨.finite x, .finite y, (ihl leftAdmitted x).mpr leftValue,
        (ihr rightAdmitted y).mpr rightValue, ?_⟩
      rcases operator with rfl | rfl
      · exact ((finite_add_iff x y result).mp arithmetic).symm
      · exact ((finite_mul_iff x y result).mp arithmetic).symm

/-- `isFinite` under partial finite arithmetic is `isFinite` of the total IEEE
result: the finiteness condition holds in the finite instantiation exactly
when the IEEE evaluation of the same term is finite. -/
theorem Condition.finite_holds_iff (term : ScalarTerm inputs outputs bounds)
    (admitted : term.Admitted) (zero one : Binary64.Value)
    (input : Env Binary64.Value inputs) (state : Signaled Binary64.Value outputs)
    (iterators : IteratorEnv bounds) :
    (Condition.finite term).Holds Finite.Result (fun _ => True) zero one @input state iterators ↔
      (Condition.finite term).Holds numberStep (fun value => value.isFinite = true)
        (.finite zero) (.finite one) (Env.numbers @input) ⟨Env.numbers state.1, state.2⟩ iterators := by
  simp only [Condition.Holds, and_true]
  constructor
  · rintro ⟨result, evaluated⟩
    exact ⟨.finite result, (term.number_eval_finite_iff admitted zero one input state.1 iterators
      result).mpr evaluated, rfl⟩
  · rintro ⟨value, evaluated, finite⟩
    obtain ⟨result, rfl⟩ := (Float64.Number.isFinite_iff value).mp finite
    exact ⟨result, (term.number_eval_finite_iff admitted zero one input state.1 iterators
      result).mp evaluated⟩

end Rumoca.GALEC
