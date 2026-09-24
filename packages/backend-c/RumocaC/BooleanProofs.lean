import RumocaC.Body

/-! The shared ordered disjunction and composition lemmas for Boolean-valued
expressions in the shared C execution model. These use its existing
short-circuit rules. -/
namespace Rumoca.CTree

/-- Ordered lazy disjunction, right-nested: `[a, b, c]` is `(a || (b || c))`
and `[a]` is `a`. Only the listed operands are operands of `||`, so no integer
constant is a logical operand (MISRA C:2025 Rule 10.1). The empty disjunction
is the essentially Boolean constant expression `(0 != 0)` (Appendix D.6.4,
D.7.3). -/
@[simp] def Expr.disjunction : List Expr → Expr
  | [] => .bin .ne (.nat 0) (.nat 0)
  | [e] => e
  | e :: f :: rest => .bin .or e (Expr.disjunction (f :: rest))

end Rumoca.CTree

namespace Rumoca.CBody.BoolProofs
open CTree CMemory
variable [interface : CInterface]

theorem eval_and (ha : eval env heap a = some (boolean x))
    (hb : eval env heap b = some (boolean y)) :
    eval env heap (.bin .and a b) = some (boolean (x && y)) := by
  cases x <;> simp [eval, evalWith, ha, hb]

theorem eval_or (ha : eval env heap a = some (boolean x))
    (hb : eval env heap b = some (boolean y)) :
    eval env heap (.bin .or a b) = some (boolean (x || y)) := by
  cases x <;> simp [eval, evalWith, ha, hb]

theorem eval_not (ha : eval env heap a = some (boolean x)) :
    eval env heap (.not a) = some (boolean (!x)) := by simp [eval, evalWith, ha]

/-- A disjunction of Boolean-valued operands evaluates, left to right and
lazily, to the Boolean disjunction of their values. -/
theorem eval_disjunction {α : Type} (xs : List α) (f : α → Expr) (p : α → Bool)
    (values : ∀ x ∈ xs, eval env heap (f x) = some (boolean (p x))) :
    eval env heap (Expr.disjunction (xs.map f)) = some (boolean (xs.any p)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have head := values x (by simp)
    cases rest with
    | nil => simpa [Expr.disjunction] using head
    | cons y ys =>
      have tail := ih (fun z member => values z (List.mem_cons_of_mem _ member))
      simpa [Expr.disjunction, List.any_cons] using eval_or head tail
end Rumoca.CBody.BoolProofs
