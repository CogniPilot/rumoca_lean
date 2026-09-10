import RumocaC.Body

/-! Composition lemmas for Boolean-valued expressions in the shared C
execution model. These use its existing short-circuit rules. -/
namespace Rumoca.CBody.BoolProofs
open CTree CMemory
variable [interface : CInterface]

theorem eval_and (ha : eval env heap a = some (boolean x))
    (hb : eval env heap b = some (boolean y)) :
    eval env heap (.bin .and a b) = some (boolean (x && y)) := by
  cases x <;> simp [eval, ha, hb]

theorem eval_or (ha : eval env heap a = some (boolean x))
    (hb : eval env heap b = some (boolean y)) :
    eval env heap (.bin .or a b) = some (boolean (x || y)) := by
  cases x <;> simp [eval, ha, hb]

theorem eval_not (ha : eval env heap a = some (boolean x)) :
    eval env heap (.not a) = some (boolean (!x)) := by simp [eval, ha]
end Rumoca.CBody.BoolProofs
