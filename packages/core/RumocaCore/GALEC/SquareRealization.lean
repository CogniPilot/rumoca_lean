import RumocaCore.GALEC.CoefficientRealization
import RumocaCore.Array.ADFiniteSquare

/-! The existing square coefficient program, not a new AD transformation.
All results quantify over the nominal shape, including empty tensors. -/
namespace Rumoca.GALEC.Coefficients
open Rumoca Rumoca.Tensor Rumoca.Solve.Tensor

def doubledInput : ScalarExpr := .binary .add .input .input

def squaredInput : ScalarExpr := .binary .mul .input .input

/-- The prepared pointwise square RHS and the scalar-loop interpretation have
exactly the same finite executions, for all shapes and prior output contents. -/
theorem square_rhs_loop_iff (state input initial result : Value Binary64.Value shape) :
    Finite.Executes (ArrayProfile.squareProgram shape)
      (ArrayProfile.environment state input) result ↔
    Iteration.Executes (fun i => squaredInput.Writes input[i] i)
      shape.volume initial result := by
  rw [ArrayProfile.square_finite_correct, ScalarExpr.pointwise_executes_iff]
  apply forall_congr'
  intro i
  change Finite.Result .mul input[i] input[i] result[i] ↔ _
  simpa only [ScalarExpr.executes_iff, squaredInput, ScalarExpr.inDomain,
    ScalarExpr.eval, true_and] using
      (Finite.result_iff .mul input[i] input[i] result[i])

def inputRef (shape : Shape) : Ref [shape, shape] shape := .there .here

theorem environment_eta (env : Env α [shape, shape]) :
    @ArrayProfile.environment α shape (env .here) (env (inputRef shape)) = @env := by
  funext s r
  cases r with
  | here => rfl
  | there r =>
    cases r with
    | here => rfl
    | there r => nomatch r

/-- The compact abstract equality needs an arithmetic law. It does not follow
for arbitrary ScalarOps, nor does it assert finite execution. -/
theorem square_evaluator_of_unit_products (shape : Shape) (ops : ScalarOps α)
    (zero one : α)
    (law : ∀ x, ops.add (ops.mul x one) (ops.mul x one) = ops.add x x) :
    EvaluatorRealization (ArrayProfile.squareJacobianProgram shape)
      (inputRef shape) doubledInput ops zero one where
  coefficients := by
    intro env
    rw [← environment_eta env, ArrayProfile.square_coefficients_eval]
    apply Value.ext
    intro i hi
    simpa only [BinaryOp.jvp, BinaryOp.eval, BinaryOp.scalar,
      Value.getElem_zipWith, Value.getElem_fill, ScalarExpr.pointwise,
      Value.getElem_mapWith, doubledInput, ScalarExpr.eval, inputRef,
      ArrayProfile.environment, Env.push] using law (env (inputRef shape))[i]

noncomputable section

theorem square_real_evaluator (shape : Shape) :
    EvaluatorRealization (ArrayProfile.squareJacobianProgram shape)
      (inputRef shape) doubledInput AD.realOps (0 : ℝ) 1 :=
  square_evaluator_of_unit_products shape AD.realOps 0 1
    (by intro x; simp [AD.realOps])

/-- Equality of finite value encodings, including signed zero, without claiming
that the program executes on every input to its total mathematical evaluator. -/
theorem square_finite_evaluator (shape : Shape) :
    EvaluatorRealization (ArrayProfile.squareJacobianProgram shape)
      (inputRef shape) doubledInput Finite.ops Binary64.positiveZero Binary64.one where
  coefficients := by
    intro env
    rw [← environment_eta env]
    apply Value.ext
    intro i hi
    simpa only [ScalarExpr.pointwise, Value.getElem_mapWith, doubledInput,
      ScalarExpr.eval, BinaryOp.scalar, Finite.ops, inputRef,
      ArrayProfile.environment, Env.push] using
      ArrayProfile.ADExact.coefficients_eval_get
        (env .here) (env (inputRef shape)) ⟨i, hi⟩

/-- The otherwise unused primal multiplication stays in the executable domain. -/
def squarePrimal (shape : Shape) (env : Env Binary64.Value [shape, shape]) : Prop :=
  ∀ i : Fin shape.volume,
    Binary64.finiteProduct (env (inputRef shape))[i] (env (inputRef shape))[i]

theorem square_finite_realization (shape : Shape) :
    FiniteRealization (ArrayProfile.squareJacobianProgram shape)
      (inputRef shape) doubledInput (squarePrimal shape) where
  evaluator := square_finite_evaluator shape
  domain := by
    intro env
    rw [← environment_eta env]
    simpa only [squarePrimal, inputRef, ArrayProfile.environment, Env.push,
      doubledInput, ScalarExpr.inDomain, ScalarExpr.eval, true_and] using
      ArrayProfile.ADExact.coefficients_domain
        (env .here) (env (inputRef shape))

/-- Useful loop-consumer endpoint: exact scalar expression executions plus the
retained primal domain, for arbitrary state/input/result values of this shape. -/
theorem square_executes_iff (state input result : Value Binary64.Value shape) :
    Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state input) result ↔
    (∀ i : Fin shape.volume, Binary64.finiteProduct input[i] input[i]) ∧
      ∀ i : Fin shape.volume, doubledInput.Executes input[i] result[i] := by
  simpa only [squarePrimal, inputRef, ArrayProfile.environment, Env.push] using
    (square_finite_realization shape).executes_iff
      (ArrayProfile.environment state input) result

/-- Independent Adds specification, preserving both primal and addition checks. -/
theorem square_executes_iff_adds (state input result : Value Binary64.Value shape) :
    Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state input) result ↔
    (∀ i : Fin shape.volume, Binary64.finiteProduct input[i] input[i]) ∧
      ∀ i : Fin shape.volume, Binary64.Adds input[i] input[i] (.finite result[i]) :=
  ArrayProfile.ADExact.coefficients_executes_iff state input result

/-- Exact output encodings are a consequence of execution, not just Real equality. -/
theorem square_result_bits (state input result : Value Binary64.Value shape)
    (executed : Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state input) result) (i : Fin shape.volume) :
    Binary64.toBits result[i] = Binary64.toBits (Binary64.roundedAdd input[i] input[i]) := by
  rw [ArrayProfile.ADExact.coefficients_exact state input result executed i]

/-- Finite RHS execution supplies the retained primal condition and all finite
addition outcomes; it is not weakened to just existence of finite doubling. -/
theorem square_from_finite_rhs (state input rhs : Value Binary64.Value shape)
    (executed : Finite.Executes (ArrayProfile.squareProgram shape)
      (ArrayProfile.environment state input) rhs) :
    let result := doubledInput.pointwise Finite.ops Binary64.positiveZero Binary64.one input
    Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state input) result ∧
    (∀ i : Fin shape.volume, Binary64.finiteProduct input[i] input[i]) ∧
    (∀ i : Fin shape.volume, Binary64.Adds input[i] input[i] (.finite result[i])) ∧
    (∀ i : Fin shape.volume, doubledInput.Executes input[i] result[i]) := by
  have he := ArrayProfile.ADExact.coefficients_from_finite_rhs state input rhs executed
  rw [(square_finite_evaluator shape).coefficients (ArrayProfile.environment state input)] at he
  have adds := (square_executes_iff_adds state input _).mp he
  have scalars := (square_executes_iff state input _).mp he
  exact ⟨he, adds.1, adds.2, scalars.2⟩

/-- Exact two-phase execution of the prepared square Jacobian, retaining the
primal-square condition. The output starts with arbitrary matrix contents. -/
theorem square_materializes_iff (state input : Value Binary64.Value shape)
    (initial final : Value Binary64.Value (matrixShape shape.volume shape.volume)) :
    ((∀ i : Fin shape.volume, Binary64.finiteProduct input[i] input[i]) ∧
      doubledInput.Materializes input initial final) ↔
    Finite.InDomain (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state input) ∧
    final = (ArrayProfile.squareJacobianProgram shape).eval
      Finite.ops Binary64.positiveZero Binary64.one
      (ArrayProfile.environment state input) := by
  simpa only [squarePrimal, inputRef, ArrayProfile.environment, Env.push] using
    (square_finite_realization shape).materializes_iff
      (ArrayProfile.environment state input) initial final

/-- The source RHS execution provides all domains needed by the coefficient
loop; no additional finite-addition premise is imposed on the caller. -/
theorem square_materializes_from_rhs (state input rhs : Value Binary64.Value shape)
    (executed : Finite.Executes (ArrayProfile.squareProgram shape)
      (ArrayProfile.environment state input) rhs)
    (initial : Value Binary64.Value (matrixShape shape.volume shape.volume)) :
    doubledInput.Materializes input initial
      ((ArrayProfile.squareJacobianProgram shape).eval
        Finite.ops Binary64.positiveZero Binary64.one
        (ArrayProfile.environment state input)) := by
  have coefficients := ArrayProfile.ADExact.coefficients_from_finite_rhs state input rhs executed
  exact ((square_materializes_iff state input initial _).mpr
    ⟨(Finite.executes_sound coefficients).1, rfl⟩).2

end
end Rumoca.GALEC.Coefficients
