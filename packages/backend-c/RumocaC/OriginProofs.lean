import RumocaC.Origins

namespace Rumoca.CTree

theorem Expr.Origins.every_root (origins : Expr.Origins table expr)
    (check : Origin table → Prop) (checked : origins.Every check) : check origins.root := by
  cases origins <;> simp only [Every, root] at checked ⊢ <;>
    first | exact checked | exact checked.1

mutual
theorem Expr.Origins.every_mono (origins : Expr.Origins table expr)
    (before after : Origin table → Prop) (implies : ∀ ref, before ref → after ref)
    (checked : origins.Every before) : origins.Every after := by
  cases origins with
  | id ref | nat ref | decimal ref | str ref =>
    simp only [Every] at checked ⊢
    exact implies ref checked
  | bin operation left right | index operation left right =>
    simp only [Every] at checked ⊢
    exact ⟨implies _ checked.1, every_mono left before after implies checked.2.1,
      every_mono right before after implies checked.2.2⟩
  | not operation value | deref operation value | address operation value =>
    simp only [Every] at checked ⊢
    exact ⟨implies _ checked.1, every_mono value before after implies checked.2⟩
  | field operation member value | cast operation member value =>
    simp only [Every] at checked ⊢
    exact ⟨implies _ checked.1, implies _ checked.2.1,
      every_mono value before after implies checked.2.2⟩
  | call operation callee arguments =>
    simp only [Every] at checked ⊢
    exact ⟨implies _ checked.1, every_mono callee before after implies checked.2.1,
      everyList_mono arguments before after implies checked.2.2⟩
  | sizeof operation typeName =>
    simp only [Every] at checked ⊢
    exact ⟨implies _ checked.1, implies _ checked.2⟩

theorem Expr.Origins.everyList_mono (origins : OriginList (Expr.Origins table) args)
    (before after : Origin table → Prop) (implies : ∀ ref, before ref → after ref)
    (checked : EveryList before origins) : EveryList after origins := by
  cases origins with
  | nil => simp only [EveryList]
  | cons head tail =>
    simp only [EveryList] at checked ⊢
    exact ⟨every_mono head before after implies checked.1,
      everyList_mono tail before after implies checked.2⟩
end

end Rumoca.CTree
