import RumocaC.TreePreprocessing
import RumocaFMI3.Runtime

/-! Instantiate the reusable character-rewrite proof for the existing FMI
adapter bodies. Public type/name spellings are explicit premises. These
theorems do not prove C tokenization, header expansion or FMI execution. -/
namespace Rumoca.FMI3.RuntimePreprocessing
open CTree Preprocessing

private theorem plain_iff_all (text : List Char) :
    Plain text ↔ text.all (fun c => c != '?' && c != '\\') = true := by
  simp [Plain, List.all_eq_true]

private theorem any_inputs (values : List Expr) :
    ExprInputs (Runtime.any values) ↔ ∀ value ∈ values, ExprInputs value := by
  induction values with
  | nil => simp [Runtime.any, Runtime.n, ExprInputs]
  | cons value values ih =>
      simpa [Runtime.any, Runtime.either, ExprInputs] using and_congr Iff.rfl ih

private theorem allowed_inputs (command : Command) :
    ExprInputs (Runtime.allowedExpression command) := by
  simp [Runtime.allowedExpression, Runtime.either, Runtime.both, Runtime.eqv,
    Runtime.field, Runtime.mode, Runtime.n, Runtime.v, ExprInputs, plain_iff_all, any_inputs]

private theorem require_inputs (command : Command) :
    ∀ stmt ∈ Runtime.require command, StmtInputs stmt := by
  simp [Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.branch, Runtime.negate, Runtime.fail, Runtime.ret, Runtime.call,
    Runtime.v, Expr.nullPointer, StmtInputs, ExprInputs, plain_iff_all, allowed_inputs]

set_option maxHeartbeats 1000000 in
theorem body_inputs (model : Solve.FMI3Model source) (signature : Signature) :
    ∀ stmt ∈ Runtime.body model signature, StmtInputs stmt := by
  unfold Runtime.body
  split <;> simp [StmtInputs, ExprInputs, Expr.nullPointer, plain_iff_all, or_imp, forall_and,
    Runtime.makeInstance, Runtime.instancePrefix, Runtime.countLoop,
    Runtime.getFloat64, Runtime.setFloat64, Runtime.setFloat64Values,
    Runtime.scalarAccessCheck, Runtime.pointerCheck,
    Runtime.doStep, Runtime.initialTime, Runtime.eventTime, Runtime.completedTime,
    Runtime.invalidTime, CInitialization.Emission.statement, CInitialization.value,
    Runtime.raiseField, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
    Runtime.put, Runtime.out, Runtime.ok, Runtime.setMode, Runtime.log,
    Runtime.v, Runtime.n, Runtime.call, Runtime.field, Runtime.x,
    Runtime.eqv, Runtime.nev, Runtime.lt, Runtime.gt, Runtime.le,
    Runtime.both, Runtime.either, Runtime.negate, Runtime.finite, Runtime.mode,
    Runtime.modeGuard, allowed_inputs, any_inputs]
  all_goals try exact require_inputs _
  all_goals
    split <;> simp [StmtInputs, ExprInputs, plain_iff_all, or_imp, forall_and]
  all_goals exact require_inputs _

theorem function_inputs (model : Solve.FMI3Model source) (signature : Signature)
    (valid : SignatureInputs signature) : FunctionInputs (Runtime.function model signature) :=
  ⟨valid, body_inputs model signature⟩

theorem function_preprocessed (model : Solve.FMI3Model source) (signature : Signature)
    (valid : SignatureInputs signature)
    (steps : Relation.ReflTransGen CString.Rewrite
      (Runtime.function model signature).render.toList out) :
    out = (Runtime.function model signature).render.toList :=
  Preprocessing.function_preprocessed _ (function_inputs model signature valid) steps

end Rumoca.FMI3.RuntimePreprocessing
