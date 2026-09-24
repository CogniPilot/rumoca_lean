import RumocaC.Body
import RumocaC.CountConditionCode

/-! Canonical count-condition laws, including failed evaluation and skipped
operands. These do not establish native promotions or essential-type judgments. -/
noncomputable section
namespace Rumoca.CCountConditions
open CTree CMemory CBody

/-- Failure is included; non-integer successful values are deliberately excluded. -/
def IntegerResult (result : Option Value) : Prop :=
  result = none ∨ ∃ n : Int, result = some (.integer n)

theorem sizeZero_render : sizeZero.render = "((size_t)0)" := by
  simp [sizeZero, Expr.render, Nat.repr_eq_ofList_toDigits, Nat.toDigits_zero]
theorem nonzero_render (count : Expr) :
    (nonzero count).render = "(" ++ count.render ++ " != ((size_t)0))" := by
  simp [nonzero, Expr.render, BinOp.render, sizeZero, String.append_assoc,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits_zero]

variable [interface : CInterface]
variable (declarations : CDeclaredMembers.Declarations) (objects : CDeclaredMembers.Objects)
variable (env : Locals) (heap : Heap)

theorem size_zero_eval (sizeType : interface.types "size_t" = some .size) :
    evalWith declarations objects env heap sizeZero = some (.integer 0) := by
  simp [sizeZero, evalWith, expressionCast, zeroLiteral, CBody.cast, sizeType, convert]

theorem nonzero_failed (count : Expr)
    (failed : evalWith declarations objects env heap count = none) :
    evalWith declarations objects env heap (nonzero count) = none := by
  simp [nonzero, evalWith, failed]

theorem nonzero_truth (count : Expr)
    (sizeType : interface.types "size_t" = some .size)
    (integer : IntegerResult (evalWith declarations objects env heap count)) :
    (evalWith declarations objects env heap (nonzero count)).bind Value.truth =
      (evalWith declarations objects env heap count).bind Value.truth := by
  have zero := size_zero_eval declarations objects env heap sizeType
  rcases integer with failed | ⟨n, loaded⟩
  · simp [nonzero, evalWith, failed]
  · by_cases h : n = 0 <;>
      simp [nonzero, evalWith, loaded, zero, comparison, boolean, Value.truth, h]

/-- Congruence of complete optional values through lazy disjunction. -/
theorem or_eval_congr (left other right otherRight : Expr)
    (sameLeft : evalWith declarations objects env heap left =
      evalWith declarations objects env heap other)
    (sameRight : evalWith declarations objects env heap right =
      evalWith declarations objects env heap otherRight) :
    evalWith declarations objects env heap (.bin .or left right) =
      evalWith declarations objects env heap (.bin .or other otherRight) := by
  exact congrArg₂ (fun a b : Option Value => do
    let flag ← (← a).truth
    if flag then some (boolean true)
    else return boolean (← (← b).truth)) sameLeft sameRight

/-- Full optional-result congruence; the right operand need not evaluate. -/
theorem and_truth_congr (left other right : Expr)
    (same : (evalWith declarations objects env heap left).bind Value.truth =
      (evalWith declarations objects env heap other).bind Value.truth) :
    evalWith declarations objects env heap (.bin .and left right) =
      evalWith declarations objects env heap (.bin .and other right) := by
  have lifted := congrArg (fun truth : Option Bool => truth.bind fun flag =>
    if !flag then some (boolean false)
    else do return boolean (← (← evalWith declarations objects env heap right).truth)) same
  simpa only [evalWith, Option.bind_assoc] using lifted

theorem or_truth_congr (left other right : Expr)
    (same : (evalWith declarations objects env heap left).bind Value.truth =
      (evalWith declarations objects env heap other).bind Value.truth) :
    evalWith declarations objects env heap (.bin .or left right) =
      evalWith declarations objects env heap (.bin .or other right) := by
  have lifted := congrArg (fun truth : Option Bool => truth.bind fun flag =>
    if flag then some (boolean true)
    else do return boolean (← (← evalWith declarations objects env heap right).truth)) same
  simpa only [evalWith, Option.bind_assoc] using lifted

theorem and_nonzero_eval (count right : Expr)
    (sizeType : interface.types "size_t" = some .size)
    (integer : IntegerResult (evalWith declarations objects env heap count)) :
    evalWith declarations objects env heap (.bin .and (nonzero count) right) =
      evalWith declarations objects env heap (.bin .and count right) := by
  exact and_truth_congr declarations objects env heap (nonzero count) count right
    (nonzero_truth declarations objects env heap count sizeType integer)

theorem or_nonzero_eval (count right : Expr)
    (sizeType : interface.types "size_t" = some .size)
    (integer : IntegerResult (evalWith declarations objects env heap count)) :
    evalWith declarations objects env heap (.bin .or (nonzero count) right) =
      evalWith declarations objects env heap (.bin .or count right) := by
  exact or_truth_congr declarations objects env heap (nonzero count) count right
    (nonzero_truth declarations objects env heap count sizeType integer)

theorem zero_short_circuit (count right : Expr)
    (sizeType : interface.types "size_t" = some .size)
    (loaded : evalWith declarations objects env heap count = some (.integer 0)) :
    evalWith declarations objects env heap (.bin .and (nonzero count) right) =
      some (boolean false) := by
  rw [and_nonzero_eval declarations objects env heap count right sizeType (Or.inr ⟨0, loaded⟩)]
  simp [evalWith, loaded, Value.truth]

/-- Exact same branch next-state, including failure, arbitrary tails and heap. -/
theorem branch_next (count : Expr) (yes no rest : List Stmt)
    (sizeType : interface.types "size_t" = some .size)
    (integer : IntegerResult (evalWith declarations objects env heap count)) :
    nextWith (declaredExpressions declarations objects)
      (.running (.branch (nonzero count) yes no :: rest) env heap) =
    nextWith (declaredExpressions declarations objects)
      (.running (.branch count yes no :: rest) env heap) := by
  have same := nonzero_truth declarations objects env heap count sizeType integer
  have lifted := congrArg (fun truth : Option Bool => truth.bind fun flag =>
    some (State.running ((if flag then yes else no) ++ rest) env heap)) same
  simpa only [nextWith, declaredExpressions, Option.bind_assoc] using lifted

/-- The extra lookup is a real obligation, even when a zero count skips a pointer. -/
theorem missing_type_obstruction (count : Expr)
    (missing : interface.types "size_t" = none)
    (loaded : evalWith declarations objects env heap count = some (.integer 0)) :
    (evalWith declarations objects env heap count).bind Value.truth = some false ∧
      evalWith declarations objects env heap (nonzero count) = none := by
  simp [loaded, Value.truth, nonzero, evalWith, sizeZero, expressionCast,
    zeroLiteral, CBody.cast, missing]

end Rumoca.CCountConditions
