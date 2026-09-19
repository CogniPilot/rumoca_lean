import RumocaCore.Solve.Tensor
import RumocaCore.Real.Multiplication
import RumocaCore.Real.Subtraction
import RumocaCore.Real.Division

/-! Ordered finite binary64 execution of typed tensor programs. Every binary
instruction checks all of its coordinates before execution continues. The
inductive execution relation uses independent scalar rounding specifications;
the evaluator theorem characterizes both its domain and its unique result.
These semantics prepare the C simulation obligation without adding source
syntax, choosing a solver or assuming native Float behavior. -/
noncomputable section
namespace Rumoca.Solve.Tensor.Finite
open Rumoca.Tensor

abbrev Number := Binary64.Value

def ops : ScalarOps Number :=
  ⟨Binary64.roundedAdd, Binary64.roundedMul, Binary64.roundedSub, Binary64.roundedDiv, Binary64.negate⟩

def Domain (op : BinaryOp) (a b : Number) : Prop :=
  match op with
  | .add => -Binary64.overflowUnits < Binary64.units a + Binary64.units b ∧
      Binary64.units a + Binary64.units b < Binary64.overflowUnits
  | .mul => Binary64.finiteProduct a b
  | .sub => -Binary64.overflowUnits < Binary64.units a - Binary64.units b ∧
      Binary64.units a - Binary64.units b < Binary64.overflowUnits
  | .div => Binary64.finiteQuotient a b

/-- Addition's only negative-zero result is the sum of two negative zeros;
subtraction's is `(-0) - (+0)`. Exact cancellation otherwise uses the canonical
nearest/even specification. Multiplication and division use their separate
proved product/quotient and zero-sign relations. -/
def Result (op : BinaryOp) (a b result : Number) : Prop :=
  Domain op a b ∧ match op with
    | .add => if a = Binary64.negativeZero ∧ b = Binary64.negativeZero then
        result = Binary64.negativeZero
      else Binary64.RoundsNearestEven (Binary64.units a + Binary64.units b) result
    | .mul => Binary64.ProductRoundsNearestEven a b result
    | .sub => if a = Binary64.negativeZero ∧ b = Binary64.positiveZero then
        result = Binary64.negativeZero
      else Binary64.RoundsNearestEven (Binary64.units a - Binary64.units b) result
    | .div => Binary64.QuotientRoundsNearestEven a b result

theorem result_iff (op : BinaryOp) (a b result : Number) :
    Result op a b result ↔ Domain op a b ∧ result = op.scalar ops a b := by
  apply and_congr_right
  intro _
  cases op with
  | add =>
    by_cases hz : a = Binary64.negativeZero ∧ b = Binary64.negativeZero
    · simp only [BinaryOp.scalar, ops, Binary64.roundedAdd, if_pos hz]
    · simp only [BinaryOp.scalar, ops, Binary64.roundedAdd, if_neg hz]
      exact ⟨fun h => Binary64.rounding_unique h (Binary64.round_spec _),
        fun h => h ▸ Binary64.round_spec _⟩
  | mul =>
    exact ⟨fun h => Binary64.product_rounding_unique h (Binary64.roundedMul_spec a b),
      fun h => h ▸ Binary64.roundedMul_spec a b⟩
  | sub =>
    by_cases hz : a = Binary64.negativeZero ∧ b = Binary64.positiveZero
    · simp only [BinaryOp.scalar, ops, Binary64.roundedSub, if_pos hz]
    · simp only [BinaryOp.scalar, ops, Binary64.roundedSub, if_neg hz]
      exact ⟨fun h => Binary64.rounding_unique h (Binary64.round_spec _),
        fun h => h ▸ Binary64.round_spec _⟩
  | div =>
    exact ⟨fun h => Binary64.quotient_rounding_unique h (Binary64.roundedDiv_spec a b),
      fun h => h ▸ Binary64.roundedDiv_spec a b⟩

def Pointwise (op : BinaryOp) (a b result : Value Number shape) : Prop :=
  ∀ i : Fin shape.volume, Result op a[i] b[i] result[i]

theorem pointwise_iff (op : BinaryOp) (a b result : Value Number shape) :
    Pointwise op a b result ↔
      (∀ i : Fin shape.volume, Domain op a[i] b[i]) ∧ result = op.eval ops a b := by
  constructor
  · intro h
    refine ⟨fun i => (result_iff _ _ _ _).mp (h i) |>.1, ?_⟩
    apply Value.ext
    intro i hi
    have he := ((result_iff _ _ _ _).mp (h ⟨i, hi⟩)).2
    simpa only [BinaryOp.eval, Value.getElem_zipWith] using he
  · rintro ⟨domain, rfl⟩ i
    apply (result_iff _ _ _ _).mpr
    exact ⟨domain i, BinaryOp.eval_correct ops op a b i⟩

def InDomain : Program Γ shape → Env Number Γ → Prop
  | .ret _, _ => True
  | .fill shape value next, env =>
      InDomain next (Env.push (Value.fill shape (value.eval Binary64.positiveZero Binary64.one)) env)
  | .binary op left right next, env =>
      (∀ i : Fin _, Domain op (env left)[i] (env right)[i]) ∧
        InDomain next (Env.push (op.eval ops (env left) (env right)) env)

/-- No result exists when any ordered instruction overflows, including an
intermediate instruction whose register is not subsequently used. -/
inductive Executes : {Γ : List Shape} → {shape : Shape} →
    Program Γ shape → Env Number Γ → Value Number shape → Prop where
  | ret {Γ : List Shape} {shape : Shape} {ref : Ref Γ shape} {env : Env Number Γ} :
      Executes (.ret ref) env (env ref)
  | fill {Γ : List Shape} {shape output : Shape} {value : Literal}
      {next : Program (shape :: Γ) output} {env : Env Number Γ} {result : Value Number output} :
      Executes next
      (Env.push (Value.fill shape (value.eval Binary64.positiveZero Binary64.one)) env) result →
      Executes (.fill shape value next) env result
  | binary {Γ : List Shape} {shape output : Shape} {op : BinaryOp} {left right : Ref Γ shape}
      {next : Program (shape :: Γ) output} {env : Env Number Γ}
      {intermediate : Value Number shape} {result : Value Number output} :
      Pointwise op (env left) (env right) intermediate →
      Executes next (Env.push intermediate env) result →
      Executes (.binary op left right next) env result

theorem executes_sound (h : Executes p env result) :
    InDomain p env ∧ result = p.eval ops Binary64.positiveZero Binary64.one env := by
  induction h with
  | ret => exact ⟨trivial, rfl⟩
  | fill _ ih => exact ih
  | binary hp _ ih =>
    obtain ⟨hd, he⟩ := (pointwise_iff _ _ _ _).mp hp
    rw [he] at ih
    exact ⟨⟨hd, ih.1⟩, ih.2⟩

theorem execute_of_domain (p : Program Γ shape) (env : Env Number Γ) :
    InDomain p env → Executes p env (p.eval ops Binary64.positiveZero Binary64.one env) := by
  induction p with
  | ret => intro _; exact .ret
  | fill shape value next ih => intro h; exact .fill (ih _ h)
  | binary op left right next ih =>
    rintro ⟨hd, hn⟩
    exact .binary ((pointwise_iff _ _ _ _).mpr ⟨hd, rfl⟩) (ih _ hn)

theorem executes_iff (p : Program Γ shape) (env : Env Number Γ) (result : Value Number shape) :
    Executes p env result ↔ InDomain p env ∧ result = p.eval ops Binary64.positiveZero Binary64.one env := by
  constructor
  · exact executes_sound
  · rintro ⟨domain, rfl⟩
    exact execute_of_domain p env domain

theorem execution_complete (p : Program Γ shape) (env : Env Number Γ) :
    (∃ result, Executes p env result) ↔ InDomain p env := by
  constructor
  · rintro ⟨result, h⟩; exact ((executes_iff _ _ _).mp h).1
  · intro h
    exact ⟨_, (executes_iff _ _ _).mpr ⟨h, rfl⟩⟩

theorem execution_unique (ha : Executes p env a) (hb : Executes p env b) : a = b :=
  ((executes_iff _ _ _).mp ha).2.trans ((executes_iff _ _ _).mp hb).2.symm

end Rumoca.Solve.Tensor.Finite
